#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Code for conflict analysis, i.e., to generate the first UIP clause.  The
// main function is 'analyze' below.  It further uses 'minimize' to minimize
// the first UIP clause, which is in 'minimize.cpp'.  An important side
// effect of conflict analysis is to update the decision queue by bumping
// variables.  Similarly analyzed clauses are bumped to mark them as active.

/*------------------------------------------------------------------------*/

void Internal::learn_empty_clause () {
  assert (!unsat);
  LOG ("learned empty clause");
  external->check_learned_empty_clause ();
  if (proof) proof->add_derived_empty_clause ();
  unsat = true;
}

void Internal::learn_unit_clause (int lit) {
  LOG ("learned unit clause %d", lit);
  external->check_learned_unit_clause (lit);
  if (proof) proof->add_derived_unit_clause (lit);
  mark_fixed (lit);
}

/*------------------------------------------------------------------------*/

// Move bumped variables to the front of the (VMTF) decision queue.  The
// 'bumped' time stamp is updated accordingly.  It is used to determine
// whether the 'queue.assigned' pointer has to be moved in 'unassign'.

void Internal::bump_queue (int lit) {
  assert (opts.bump);
  const int idx = vidx (lit);
  if (!links[idx].next) return; // 如果我後繼無人, 那也沒有必要移動了。
  queue.dequeue (links, idx); // 把這個變數拉
  queue.enqueue (links, idx); // 到 VMTF queue 的最尾端 (last 的後面)
  assert (stats.bumped != INT64_MAX);
  btab[idx] = ++stats.bumped; // 因為有 enqueue 的動作, 必須更新 timestamp
  LOG ("moved to front variable %d and bumped to %" PRId64 "", idx, btab[idx]);
  if (!vals[idx]) update_queue_unassigned (idx); // 如果最右邊的元素變成 unassigned, 為了要滿足 next-search 指標的所有右邊元素都是 assigned 的條件, 必須把此指標也跟著移到最右邊
}

/*------------------------------------------------------------------------*/

// It would be better to use 'isinf' but there are some historical issues
// with this function.  On some platforms it is a macro and even for C++ it
// changed the scope (in pre 5.0 gcc) from '::isinf' to 'std::isinf'.  I do
// not want to worry about these strange incompatibilities and thus use the
// same trick as in older solvers (since the MiniSAT team invented EVSIDS)
// and simply put a hard limit here.  It is less elegant but easy to port.

static inline bool evsids_limit_hit (double score) { // 達到天花板高度就應該開始調整 score 縮放倍率了
  assert (sizeof (score) == 8); // assume IEEE 754 64-bit double
  return score > 1e150;         // MAX_DOUBLE is around 1.8e308
}

/*------------------------------------------------------------------------*/

// Classical exponential VSIDS as pioneered by MiniSAT.

void Internal::rescore () {
  stats.rescored++;
  double divider = scinc;
  for (int idx = 1; idx <= max_var; idx++) {
    const double tmp = stab[idx];
    if (tmp > divider) divider = tmp;
  }
  PHASE ("rescore", stats.rescored,
    "rescoring %d variable scores by 1/%g", max_var, divider);
  assert (divider > 0); // 在這之前要選 divider, 為了確保除完之後每個人的 score 和 global increment score 都不超過 1, divider 只好選在這之中最大的那個數字
  double factor = 1.0 / divider; // 不懂為何要多此一舉又生一個新的變數 factor, 後面直接用 / divider 不是很好嗎?
  for (int idx = 1; idx <= max_var; idx++)
    stab[idx] *= factor; // 也可以寫成 /= divider;
  scinc *= factor; // 也可以寫成 /= divider; 這邊要特別注意, 不是只有變數 score 要 scaling, 在 bump 的時候所加的 scinc = g^i 也要一起作 (兩倍率相等的數字才能相加)
  PHASE ("rescore", stats.rescored,
    "new score increment %g after %" PRId64 " conflicts",
    scinc, stats.conflicts);
}

void Internal::bump_score (int lit) { // 我們想 bump "lit" 所對應到的變數的 score
  assert (opts.bump);
  int idx = vidx (lit);
  double old_score = score (idx);
  assert (!evsids_limit_hit (old_score)); // 開始之前先行確認 old_score 尚未摸到天花板, but why?? is it necessary??
  double new_score = old_score + scinc; // 先根據公式 s + g^i 算出 new_score
  if (evsids_limit_hit (new_score)) { // 和典型 VSIDS 不同, 這邊是快碰到天花板時才作同除的動作, 如果 new_score 達天花板...
    LOG ("bumping %g score of %d hits EVSIDS score limit", old_score, idx);
    rescore (); // 對所有變數, 包含 g^i, 的 score 作 scaling
    old_score = score (idx);
    assert (!evsids_limit_hit (old_score)); // 原本的 old_score 尚未摸到天花板, 作 scaling 之後應該也要如此
    new_score = old_score + scinc; // scaling 之後再重算一次 new_score
  }
  assert (!evsids_limit_hit (new_score)); // 因為縮放倍率是挑最大的那個數字去除, 所以 new_score <= 1 + 1 = 2 並不會達到 1e150
  LOG ("new %g score of %d", new_score, idx);
  score (idx) = new_score; // 存回新計算的分數
  if (scores.contains (idx)) scores.update (idx); // 根據新計算的分數更新 idx 在 heap 的位置
}

// Important variables recently used in conflict analysis are 'bumped',

void Internal::bump_variable (int lit) { // 依據當下的環境可以走 VMTF 或 EVSIDS 兩種模式。
  if (use_scores ()) bump_score (lit);
  else bump_queue (lit);
}

// After every conflict we increase the score increment by a factor.

void Internal::bump_scinc () { // 其實就是 g^i -> g^(i+1)
  assert (use_scores ()); // 只有在 VMTF 模式下這個函式才有意義
  assert (!evsids_limit_hit (scinc)); // 確認 scinc 尚未摸到天花板, but why?? is it necessary??
  double f = 1e3/opts.scorefactor;
  double new_scinc = scinc * f; // g^i -> g^(i+1)
  if (evsids_limit_hit (new_scinc)) { // 如果 new_scinc 很不幸地碰到了天花板
    LOG ("bumping %g increment by %g hits EVSIDS score limit", scinc, f);
    rescore (); // 將對整體數值作 scaling
    new_scinc = scinc * f; // scaling 之後再度重新計算
  }
  assert (!evsids_limit_hit (new_scinc)); // 希望不會再碰到天花板, 不過這應該不是很嚴謹, 因為我們並不知道 f 的範圍
  LOG ("bumped score increment from %g to %g with factor %g",
    scinc, new_scinc, f);
  scinc = new_scinc; // 把新結果存回原變數
}

/*------------------------------------------------------------------------*/

struct analyze_bumped_rank { // only used in line 168
  Internal * internal;
  analyze_bumped_rank (Internal * i) : internal (i) { }
  uint64_t operator () (const int & a) const {
    return internal->bumped (a);
  }
};

struct analyze_bumped_smaller { // only used in line 168
  Internal * internal;
  analyze_bumped_smaller (Internal * i) : internal (i) { }
  bool operator () (const int & a, const int & b) const {
    const auto s = analyze_bumped_rank (internal) (a);
    const auto t = analyze_bumped_rank (internal) (b);
    return s < t;
  }
};

/*------------------------------------------------------------------------*/

void Internal::bump_variables () { // only used in line 710 to bump all variables related to conflicts (這裡故意用模糊的詞彙 "related to", 因尚未弄清楚細節)

  assert (opts.bump);

  START (bump);

  if (opts.bumpreason) bump_also_all_reason_literals ();

  if (!use_scores ()) {

    // Variables are bumped in the order they are in the current decision
    // queue.  This maintains relative order between bumped variables in the
    // queue and seems to work best.  We also experimented with focusing on
    // variables of the last decision level, but results were mixed.

    MSORT (opts.radixsortlim,
      analyzed.begin (), analyzed.end (),
      analyze_bumped_rank (this), analyze_bumped_smaller (this));
  }

  for (const auto & lit : analyzed)
    bump_variable (lit);

  if (use_scores ()) bump_scinc (); // 如果是在 EVSIDS 環境下, 就還要考慮 g^i

  STOP (bump);
}

/*------------------------------------------------------------------------*/

// We use the glue time stamp table 'gtab' for fast glue computation.

int Internal::recompute_glue (Clause * c) {
  int res = 0;
  const int64_t stamp = ++stats.recomputed;
  for (const auto & lit : *c) {
    int level = var (lit).level;
    assert (gtab[level] <= stamp);
    if (gtab[level] == stamp) continue;
    gtab[level] = stamp;
    res++;
  }
  return res;
}

// Clauses resolved since the last reduction are marked as 'used', their
// glue is recomputed and they promoted if the glue shrinks.  Note that
// promotion from 'tier3' to 'tier2' will set 'used' to '2'.

inline void Internal::bump_clause (Clause * c) {
  LOG (c, "bumping");
  unsigned used = c->used;
  c->used = 1;
  if (c->keep) return;
  if (c->hyper) return;
  if (!c->redundant) return;
  int new_glue = recompute_glue (c);
  if (new_glue < c->glue) promote_clause (c, new_glue);
  else if (used && c->glue <= opts.reducetier2glue) c->used = 2;
}

/*------------------------------------------------------------------------*/

// During conflict analysis literals not seen yet either become part of the
// first unique implication point (UIP) clause (if on lower decision level),
// are dropped (if fixed), or are resolved away (if on the current decision
// level and different from the first UIP).  At the same time we update the
// number of seen literals on a decision level.  This helps conflict clause
// minimization.  The number of seen levels is the glucose level (also
// called 'glue', or 'LBD').

inline void
Internal::analyze_literal (int lit, int & open) {
  assert (lit);
  Flags & f = flags (lit);
  if (f.seen) return;
  Var & v = var (lit);
  if (!v.level) return;
  assert (val (lit) < 0);
  assert (v.level <= level);
  if (v.level < level) clause.push_back (lit);
  Level & l = control[v.level];
  if (!l.seen.count++) {
    LOG ("found new level %d contributing to conflict", v.level);
    levels.push_back (v.level);
  }
  if (v.trail < l.seen.trail) l.seen.trail = v.trail;
  f.seen = true;
  analyzed.push_back (lit);
  LOG ("analyzed literal %d assigned at level %d", lit, v.level);
  if (v.level == level) open++;
}

inline void
Internal::analyze_reason (int lit, Clause * reason, int & open) {
  assert (reason);
  bump_clause (reason);
  for (const auto & other : *reason)
    if (other != lit)
      analyze_literal (other, open);
}

/*------------------------------------------------------------------------*/

// This is an idea which was implicit in MapleCOMSPS 2016 for 'limit = 1'.

inline bool Internal::bump_also_reason_literal (int lit) {
  assert (lit);
  assert (val (lit) < 0);
  Flags & f = flags (lit);
  if (f.seen) return false;
  const Var & v = var (lit);
  if (!v.level) return false;
  f.seen = true;
  analyzed.push_back (lit);
  LOG ("bumping also reason literal %d assigned at level %d", lit, v.level);
  return true;
}

inline void Internal::bump_also_reason_literals (int lit, int limit) {
  assert (lit);
  assert (limit > 0);
  const Var & v = var (lit);
  assert (val (lit));
  if (!v.level) return;
  Clause * reason = v.reason;
  if (!reason) return;
  for (const auto & other : *reason) {
    if (other == lit)  continue;
    if (!bump_also_reason_literal (other)) continue;
    if (limit < 2) continue;
    bump_also_reason_literals (-other, limit-1);
  }
}

inline void Internal::bump_also_all_reason_literals () { // only used in line 157
  assert (opts.bumpreason);
  assert (opts.bumpreasondepth > 0);
  for (const auto & lit : clause)
    bump_also_reason_literals (-lit, opts.bumpreasondepth);
}

/*------------------------------------------------------------------------*/

void Internal::clear_analyzed_literals () {
  LOG ("clearing %zd analyzed literals", analyzed.size ());
  for (const auto & lit : analyzed) {
    Flags & f = flags (lit);
    assert (f.seen);
    f.seen = false;
    assert (!f.keep);
    assert (!f.poison);
    assert (!f.removable);
  }
  analyzed.clear ();
}

void Internal::clear_analyzed_levels () {
  LOG ("clearing %zd analyzed levels", levels.size ());
  for (const auto & l : levels)
    if (l < (int) control.size ())
      control[l].reset ();
  levels.clear ();
}

/*------------------------------------------------------------------------*/

// Smaller level and trail.  Comparing literals on their level is necessary
// for chronological backtracking, since trail order might in this case not
// respect level order.

struct analyze_trail_negative_rank {
  Internal * internal;
  analyze_trail_negative_rank (Internal * s) : internal (s) { }
  uint64_t operator () (int a) {
    Var & v = internal->var (a);
    uint64_t res = v.level;
    res <<= 32;
    res |= v.trail;
    return ~res;
  }
};

struct analyze_trail_larger {
  Internal * internal;
  analyze_trail_larger (Internal * s) : internal (s) { }
  bool operator () (const int & a, const int & b) const {
    return
      analyze_trail_negative_rank (internal) (a) <
      analyze_trail_negative_rank (internal) (b);
  }
};

/*------------------------------------------------------------------------*/

// Generate new driving clause and compute jump level.

Clause * Internal::new_driving_clause (const int glue, int & jump) {

  const size_t size = clause.size ();
  Clause * res;

  if (!size) {

    jump = 0;
    res = 0;

  } else if (size == 1) {

    iterating = true;
    jump = 0;
    res = 0;

  } else {

    assert (clause.size () > 1);

    // We have to get the last assigned literals into the watch position.
    // Sorting all literals with respect to reverse assignment order is
    // overkill but seems to get slightly faster run-time.  For 'minimize'
    // we sort the literals too heuristically along the trail order (so in
    // the opposite order) with the hope to hit the recursion limit less
    // frequently.  Thus sorting effort is doubled here.
    //
    MSORT (opts.radixsortlim,
      clause.begin (), clause.end (),
      analyze_trail_negative_rank (this), analyze_trail_larger (this));

    jump = var (clause[1]).level;
    res = new_learned_redundant_clause (glue);
    if (glue <= opts.reducetier2glue) res->used = 2;
    else res->used = 1;
  }

  LOG ("jump level %d", jump);

  return res;
}

/*------------------------------------------------------------------------*/

// If chronological backtracking is enabled we need to find the actual
// conflict level and then potentially can also reuse the conflict clause (注: 按照那篇 SAT'18 的定義這邊的 conflict clause 其實應該是 conflict"ing" clause)
// as driving clause instead of deriving a redundant new driving clause
// (forcing 'forced') if the number 'count' of literals in conflict assigned
// at the conflict level is exactly one.

inline int Internal::find_conflict_level (int & forced) { // 注意 forced 其實也是另一個回傳值

  assert (conflict);
  assert (opts.chrono);

  int res = 0, count = 0; // res: 記錄目前遇到最高級 literal 的級數; count: 記錄目前遇到最高級 literal 的個數

  forced = 0; // 記錄唯一一個最高級的 literal 為何，如果最高級 literal 有兩個以上則此值最後會歸 0

  for (const auto & lit : *conflict) {
    const int tmp = var (lit).level;
    if (tmp > res) {
      res = tmp;
      forced = lit; // 標記第一次遇到最高級的 literal
      count = 1;
    } else if (tmp == res) {
      count++;
      if (res == level && count > 1)
        break; // 這邊應該只是一個小小加速的技巧, 不影響正確性, 因為 conflict level 不可能超過 current decision level, 所以一旦摸到上界我就判定那個 literal 是最高級的, 那自然最高級 literal 不唯一的話就馬上 ban 掉。
    }
  }

  LOG ("%d literals on actual conflict level %d", count, res);

  const int size = conflict->size; // clause 有幾個 literal
  int * lits = conflict->literals; // 記錄 literal 的 array

  // Move the two highest level literals to the front.
  // 從這邊開始下面好像就跟 watch list 有關, 我都還沒弄懂這邊。
  for (int i = 0; i < 2; i++) {

    const int lit = lits[i];

    int highest_position = i;
    int highest_literal = lit;
    int highest_level = var (highest_literal).level;

    for (int j = i + 1; j < size; j++) {
      const int other = lits[j];
      const int tmp = var (other).level;
      if (highest_level >= tmp) continue;
      highest_literal = other;
      highest_position = j;
      highest_level = tmp;
      if (highest_level == res) break;
      if (i && highest_level == res - 1) break;
    }

    // No unwatched higher assignment level literal.
    //
    if (highest_position < 2) continue;

    LOG (conflict, "unwatch %d in", lit);
    remove_watch (watches (lit), conflict);
    lits[highest_position] = lit;
    lits[i] = highest_literal;
    watch_literal (highest_literal, lits[!i], conflict);
  }

  // Only if the number of highest level literals in the conflict is one
  // then we can reuse the conflict clause as driving clause for 'forced'.
  //
  if (count != 1) forced = 0; // 最高級的 literal 超過一個的話就不能用 imply 這招了!

  return res; // 回傳最高級 literal 的級數
}

/*------------------------------------------------------------------------*/

inline int Internal::determine_actual_backtrack_level (int jump) {

  int res;

  assert (level > jump);

  if (!opts.chrono) {
    res = jump; // 只考慮傳統 non-chronological 的話, 就是傳統的挑除了 1UIP 以外最高的 literal 級數
    LOG ("chronological backtracking disabled using jump level %d", res);
  } else if (opts.chronoalways) { // 在任何情況下都強迫使用新版的 chronological 的話, 就是僅比當前的 decision level 下降一層
    stats.chrono++;
    res = level - 1;
    LOG ("forced chronological backtracking to level %d", res);
  } else if (jump >= level - 1) { // 但前面又 assert (level > jump), 所以這句話其實是 jump == level - 1 的意思
    res = jump;
    LOG ("jump level identical to chronological backtrack level %d", res);
  } else if ((size_t) jump < assumptions.size ()) { // 我還不懂 assumptions 是什麼意思
    res = jump;
    LOG ("using jump level %d since it is lower than assumption level %zd",
      res, assumptions.size ());
  } else if (level - jump > opts.chronolevelim) { // 如果 non-chronological 的級數太低導致砍掉重練的成本太大，就統一改成 chronological
    stats.chrono++;
    res = level - 1;
    LOG ("back-jumping over %d > %d levels prohibited"
      "thus backtracking chronologically to level %d",
      level - jump, opts.chronolevelim, res);
  } else if (opts.chronoreusetrail) { // 否則就讓演算法幫我們挑最適合的級數, 以合理地重複使用那些已經選好的 literal

    int best_idx = 0, best_pos = 0;

    if (use_scores ()) {
      for (size_t i = control[jump + 1].trail; i < trail.size (); i++) {
        const int idx = abs (trail[i]);
        if (best_idx && !score_smaller (this) (best_idx, idx)) continue;
        best_idx = idx;
        best_pos = i;
      }
      LOG ("best variable score %g", score (best_idx));
    } else {
      for (size_t i = control[jump + 1].trail; i < trail.size (); i++) {
        const int idx = abs (trail[i]);
        if (best_idx && bumped (best_idx) >= bumped (idx)) continue;
        best_idx = idx;
        best_pos = i;
      }
      LOG ("best variable bumped %" PRId64 "", bumped (best_idx));
    }
    assert (best_idx); // 到這邊應該已經選好最棒的 literal 了, 只是我還不知道方法的細節
    LOG ("best variable %d at trail position %d", best_idx, best_pos);

    // Now find the frame and decision level in the control stack of that
    // best variable index.  Note that, as in 'reuse_trail', the frame
    // 'control[i]' for decision level 'i' contains the trail before that
    // decision level, i.e., the decision 'control[i].decision' sits at
    // 'control[i].trail' in the trail and we thus have to check the level
    // of the control frame one higher than at the result level.
    //
    res = jump;
    while (res < level-1 && control[res+1].trail <= best_pos)
      res++; // 目的僅是找出那個 best variable 的 decision level, 但我沒去驗證這個迴圈方法有沒有漏洞

    if (res == jump)
      LOG ("default non-chronological back-jumping to level %d", res);
    else {
      stats.chrono++;
      LOG ("chronological backtracking to level %d to reuse trail", res);
    }

  } else { // 如果要 opts.chrono 卻又不肯 opts.chronoreusetrail, 是不是一個奇怪的人呢?
    res = jump;
    LOG ("non-chronological back-jumping to level %d", res);
  }

  return res;
} // Question: 最後兩個 else-if 和 else 的 block 是否可合併成前者, 然後把最後一個砍掉, 這樣比較合理吧? opts.chronoreusetrail 選項應是多餘?

/*------------------------------------------------------------------------*/

void Internal::eagerly_subsume_recently_learned_clauses (Clause * c) {
  assert (opts.eagersubsume);
  LOG (c, "trying eager subsumption with");
  mark (c);
  int64_t lim = stats.eagertried + opts.eagersubsumelim;
  const auto begin = clauses.begin ();
  auto it = clauses.end ();
#ifdef LOGGING
  int64_t before = stats.eagersub;
#endif
  while (it != begin && stats.eagertried++ <= lim) {
    Clause * d =  *--it;
    if (c == d) continue;
    if (d->garbage) continue;
    if (!d->redundant) continue;
    int needed = c->size;
    for (auto & lit : *d) {
      if (marked (lit) <= 0) continue;
      if (!--needed) break;
    }
    if (needed) continue;
    LOG (d, "eager subsumed");
    stats.eagersub++;
    stats.subsumed++;
    mark_garbage (d);
  }
  unmark (c);
#ifdef LOGGING
  uint64_t subsumed = stats.eagersub - before;
  if (subsumed) LOG ("eagerly subsumed %d clauses", subsumed);
#endif
}

/*------------------------------------------------------------------------*/

// This is the main conflict analysis routine.  It assumes that a conflict
// was found.  Then we derive the 1st UIP clause, optionally minimize it,
// add it as learned clause, and then uses the clause for conflict directed
// back-jumping and flipping the 1st UIP literal.  In combination with
// chronological backtracking (see discussion above) the algorithm becomes
// slightly more involved.

void Internal::analyze () {

  START (analyze);

  assert (conflict); // 它唯二在 internal.cpp 出現的地方 (line 191, 494) 都有前提 !propagate() 必須被滿足, 所以一定有 conflicting clause

  // First update moving averages of trail height at conflict.
  //
  UPDATE_AVERAGE (averages.current.trail.fast, trail.size ());
  UPDATE_AVERAGE (averages.current.trail.slow, trail.size ());

  /*----------------------------------------------------------------------*/

  if (opts.chrono) {

    int forced; // 全意是 forced literal, 記錄哪個 literal 到最後會被 imply

    const int conflict_level = find_conflict_level (forced); // line 398, 回傳那個 conflicting clause 裡面所有 literal 的最高級數為何, 以及未來會被 imply 的 literal (若有) 為何

    // In principle we can perform conflict analysis as in non-chronological
    // backtracking except if there is only one literal with the maximum
    // assignment level in the clause.  Then standard conflict analysis is
    // unnecessary and we can use the conflict as a driving clause.  In the
    // pseudo code of the SAT'18 paper on chronological backtracking this
    // corresponds to the situation handled in line 4-6 in Alg. 1, except
    // that the pseudo code in the paper only backtracks while we eagerly
    // assign the single literal on the highest decision level.

    if (forced) { // 如果有唯一一個最高級的 literal 的話

      assert (forced);
      assert (conflict_level > 0); // 這一行我不敢保證
      LOG ("single highest level literal %d", forced);

      // The pseudo code in the SAT'18 paper actually backtracks to the
      // 'second highest decision' level, while their code backtracks
      // to 'conflict_level-1', which is more in the spirit of chronological
      // backtracking anyhow and thus we also do the latter.
      //
      backtrack (conflict_level - 1); // 這區要有 chronological 精神的話, 當然要讓 backtrack level 盡可能的高, 又必須把 highest literal 砍掉, 那當然選 conflict_level - 1

      LOG ("forcing %d", forced);
      search_assign_driving (forced, conflict); // 強迫把 forced 這個 literal 設成 true

      conflict = 0; // 因為 conflict 已經在上面處理掉了, 所以這邊旗標值應該要歸 0
      STOP (analyze);
      return; // 該做的都做了，下面的就不用再管了
    }

    // Backtracking to the conflict level is in the pseudo code in the
    // SAT'18 chronological backtracking paper, but not in their actual
    // implementation.  In principle we do not need to backtrack here. (我同意這句話!!!)
    // However, as a side effect of backtracking to the conflict level we
    // set 'level' to the conflict level which then allows us to reuse the
    // old 'analyze' code as is.  The alternative (which we also tried but
    // then abandoned) is to use 'conflict_level' instead of 'level' in the
    // analysis, which however requires to pass it to the 'analyze_reason'
    // and 'analyze_literal' functions.
    //
    backtrack (conflict_level); // 上面註解已有解釋為什麼這邊要作多餘的 backtrack, 但我還沒弄懂
  }

  // Actual conflict on root level, thus formula unsatisfiable.
  //
  if (!level) {
    learn_empty_clause ();
    STOP (analyze);
    return;
  }

  /*----------------------------------------------------------------------*/

  // First derive the 1st UIP clause by going over literals assigned on the
  // current decision level.  Literals in the conflict are marked as 'seen'
  // as well as all literals in reason clauses of already 'seen' literals on
  // the current decision level.  Thus the outer loop starts with the
  // conflict clause as 'reason' and then uses the 'reason' of the next
  // seen literal on the trail assigned on the current decision level.
  // During this process maintain the number 'open' of seen literals on the
  // current decision level with not yet processed 'reason'.  As soon 'open'
  // drops to one, we have found the first unique implication point.  This
  // is sound because the topological order in which literals are processed
  // follows the assignment order and a more complex algorithm to find
  // articulation points is not necessary.
  //
  Clause * reason = conflict;
  LOG (reason, "analyzing conflict");

  assert (clause.empty ());

  int i = trail.size ();        // Start at end-of-trail.
  int open = 0;                 // Seen but not processed on this level.
  int uip = 0;                  // The first UIP literal.

  for (;;) { // 這一大段迴圈都是在找 uip (應該是ㄅ)
    analyze_reason (uip, reason, open);
    uip = 0;
    while (!uip) {
      assert (i > 0);
      const int lit = trail[--i];
      if (!flags (lit).seen) continue;
      if (var (lit).level == level) uip = lit;
    }
    if (!--open) break;
    reason = var (uip).reason;
    LOG (reason, "analyzing %d reason", uip);
  }
  LOG ("first UIP %d", uip); // 找到 uip 了!! 但詳細的方法我還不太會...
  clause.push_back (-uip);

  // Update glue and learned (1st UIP literals) statistics.
  //
  int size = (int) clause.size ();
  const int glue = (int) levels.size () - 1; // 不太懂 glue 的意義為何?
  LOG (clause, "1st UIP size %d and glue %d clause", size, glue);
  UPDATE_AVERAGE (averages.current.glue.fast, glue);
  UPDATE_AVERAGE (averages.current.glue.slow, glue);
  stats.learned.literals += size;
  stats.learned.clauses++;
  assert (glue < size);

  // Update decision heuristics.
  //
  if (opts.bump) bump_variables (); // line 151 of analyze.cpp

  // Minimize the 1st UIP clause as pioneered by Niklas Soerensson in
  // MiniSAT and described in our joint SAT'09 paper.
  //
  if (size > 1) { // 我在想下面那一層 opts.minimize 的條件式是否可以往上拉到這一層?
    if (opts.minimize) minimize_clause ();
    size = (int) clause.size ();
  }

  // Update actual size statistics.
  //
  stats.units    += (size == 1);
  stats.binaries += (size == 2);
  UPDATE_AVERAGE (averages.current.size, size);

  // Determine back-jump level, learn driving clause, backtrack and assign
  // flipped 1st UIP literal.
  //
  int jump;
  Clause * driving_clause = new_driving_clause (glue, jump); // 這應該就是我們新學到的 learned clause 了
  UPDATE_AVERAGE (averages.current.jump, jump);

  int new_level = determine_actual_backtrack_level (jump);; // 就是 paper 虛擬碼裡面提到的 b 值, 注意這邊裡面的計算方式是已經有根據不同模式去做調整
  UPDATE_AVERAGE (averages.current.level, new_level);
  backtrack (new_level); // 既然已經算好目標高度, 當然就可以直接 backtrack 了!

  if (uip) search_assign_driving (-uip, driving_clause); // 如果有 uip 的話當然就強迫把它的反向 -uip 設成 true, 才代表我們有確實學習到新的 clause
  else learn_empty_clause (); // 不確定其正確性

  if (stable) reluctant.tick (); // Reluctant has its own 'conflict' counter. 這是什麼??

  // Clean up.
  //
  clear_analyzed_literals ();
  clear_analyzed_levels ();
  clause.clear ();
  conflict = 0; // 因為 conflict 已經在上面處理掉了, 所以這邊旗標值應該要歸 0

  STOP (analyze);

  if (driving_clause && opts.eagersubsume) // 吃吃吃, 吃吃吃, 能吃就吃
    eagerly_subsume_recently_learned_clauses (driving_clause); // 還沒閱讀其細節
}

// We wait reporting a learned unit until propagation of that unit is
// completed.  Otherwise the 'i' report gives the number of remaining
// variables before propagating the unit (and hides the actual remaining
// variables after propagating it).

void Internal::iterate () { iterating = false; report ('i'); }

}
