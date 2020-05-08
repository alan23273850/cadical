#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// We are using the address of 'decision_reason' as pseudo reason for
// decisions to distinguish assignment decisions from other assignments.
// Before we added chronological backtracking all learned units were
// assigned at decision level zero ('Solver.level == 0') and we just used a
// zero pointer as reason.  After allowing chronological backtracking units
// were also assigned at higher decision level (but with assignment level
// zero), and it was not possible anymore to just distinguish the case
// 'unit' versus 'decision' by just looking at the current level.  Both had
// a zero pointer as reason.  Now only units have a zero reason and
// decisions need to use the pseudo reason 'decision_reason'.

static Clause decision_reason_clause;
static Clause * decision_reason = &decision_reason_clause;

// If chronological backtracking is used the actual assignment level might
// be lower than the current decision level. In this case the assignment
// level is defined as the maximum level of the literals in the reason
// clause except the literal for which the clause is a reason.  This
// function determines this assignment level. For non-chronological
// backtracking as in classical CDCL this function always returns the
// current decision level, the concept of assignment level does not make
// sense, and accordingly this function can be skipped.

inline int Internal::assignment_level (int lit, Clause * reason) {

  assert (opts.chrono); // 只在 chronological 環境下才需要
  if (!reason) return level;

  int res = 0; // 記錄 clause 內除了 lit 之外最高級的 literal 的級數

  for (const auto & other : *reason) {
    if (other == lit) continue; // 自己不能決定自己的 level
    assert (val (other));
    int tmp = var (other).level;
    if (tmp > res) res = tmp;
  }

  return res; // 回傳答案
}

/*------------------------------------------------------------------------*/
// 原則上這一行就是對 reason 裡面剩下唯一的 lit 去作賦值讓整個 clause 變成 true。
inline void Internal::search_assign (int lit, Clause * reason) {

  if (level) require_mode (SEARCH);

  const int idx = vidx (lit); // 找 lit 的變數編號 (正數, 取絕對值)
  assert (!vals[idx]); // 因為我們即將對 lit 賦值, 故此時它不應該有任何值才對
  assert (!flags (idx).eliminated () || reason == decision_reason); // 這一行還沒弄懂
  Var & v = var (idx); // 取出該變數的資料結構以便更新
  int lit_level; // 這個 lit 被賦值時所對應的 level

  // The following cases are explained in the two comments above before
  // 'decision_reason' and 'assignment_level'.
  //
  if (!reason) lit_level = 0;   // unit, 沒有理由代表是天然的 implication, 故其 level 只能為 0
  else if (reason == decision_reason) lit_level = level, reason = 0; // 這一行還沒弄懂
  else if (opts.chrono) lit_level = assignment_level (lit, reason); // 找出剩下的 literal 裡面最高的級數
  else lit_level = level; // 當 non-chronological 的時候, WHY???
  if (!lit_level) reason = 0; // 如果後來發現是天然的 implication, 代表它真的不需要理由, 再次確認把 reason 設成 NULL

  v.level = lit_level; // 存變數賦值等級
  v.trail = (int) trail.size (); // 存變數賦值順序
  v.reason = reason; // 存變數賦值之理由子句, 注意這個子句的變數有包含 v 本身
  if (!lit_level) learn_unit_clause (lit);  // increases 'stats.fixed', 天然的 implication 便是一個 unit clause
  const signed char tmp = sign (lit); // 從現在開始下面 5 行, 變數前帶正號則賦予變數正號, 變數前帶負號則賦予變數負號, 總之要讓 lit 是正的
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  if (!searching_lucky_phases)
    phases.saved[idx] = tmp;                // phase saving during search, 我還沒學到這個
  trail.push_back (lit); // 已經賦值的 lit 根據定義當然要存進 trail 之中
#ifdef LOGGING
  if (!lit_level) LOG ("root-level unit assign %d @ 0", lit);
  else LOG (reason, "search assign %d @ %d", lit, lit_level);
#endif

  if (watching ()) { // 我還沒研究 watch 的結構
    const Watches & ws = watches (-lit);
    if (!ws.empty ()) {
      const Watch & w = ws[0];
      __builtin_prefetch (&w, 0, 1);
    }
  }
}

/*------------------------------------------------------------------------*/

// External versions of 'search_assign' which are not inlined.  They either
// are used to assign unit clauses on the root-level, in 'decide' to assign
// a decision or in 'analyze' to assign the literal 'driven' by a learned
// clause.  This happens far less frequently than the 'search_assign' above,
// which is called directly in 'propagate' below and thus is inlined.

void Internal::assign_unit (int lit) {
  assert (!level);
  search_assign (lit, 0);
}

// Just assume the given literal as decision (increase decision level and
// assign it).  This is used below in 'decide'.

void Internal::search_assume_decision (int lit) {
  require_mode (SEARCH);
  assert (propagated == trail.size ());
  level++;
  control.push_back (Level (lit, trail.size ()));
  LOG ("search decide %d", lit);
  search_assign (lit, decision_reason);
}

void Internal::search_assign_driving (int lit, Clause * c) {
  require_mode (SEARCH);
  search_assign (lit, c);
}

/*------------------------------------------------------------------------*/

// The 'propagate' function is usually the hot-spot of a CDCL SAT solver.
// The 'trail' stack saves assigned variables and is used here as BFS queue
// for checking clauses with the negation of assigned variables for being in
// conflict or whether they produce additional assignments.

// This version of 'propagate' uses lazy watches and keeps two watched
// literals at the beginning of the clause.  We also use 'blocking literals'
// to reduce the number of times clauses have to be visited (2008 JSAT paper
// by Chu, Harwood and Stuckey).  The watches know if a watched clause is
// binary, in which case it never has to be visited.  If a binary clause is
// falsified we continue propagating.

// Finally, for long clauses we save the position of the last watch
// replacement in 'pos', which in turn reduces certain quadratic accumulated
// propagation costs (2013 JAIR article by Ian Gent) at the expense of four
// more bytes for each clause.

bool Internal::propagate () {

  if (level) require_mode (SEARCH);
  assert (!unsat);

  START (propagate);

  // Updating statistics counter in the propagation loops is costly so we
  // delay until propagation ran to completion.
  //
  int64_t before = propagated; // 只要是 trail 位置在 propagated - 1 以前的 literal 都不用看??? 我猜是因為它們當初剛被 assign 的時候就已經 propagate 過一次了, 而現在又有新的 assigned variable 要作 propagation, 自然沒有舊變數的份。

  while (!conflict && propagated != trail.size ()) { // 在還沒發現 conflicting clause 的情況下, 持續地遍歷 trail 裡的各個 "剛 assign 成 true" 的 literal. 順帶一提, 上面一行是不是建議可以塞一個 assert(!conflict); 呢?

    const int lit = -trail[propagated++]; // 我們當前要觀察的 literal (要注意到會放在 trail 裡的 literal 必定是 true)
    LOG ("propagating %d", -lit);
    Watches & ws = watches (lit); // 如果 lit 是 true, 那我們就想檢查那些包含 -lit (是 false) 的 clauses 有沒有 conflict 或跑 BCP 的可能

    const const_watch_iterator eow = ws.end (); // eow stands for "end of watch"?
    const_watch_iterator i = ws.begin ();
    watch_iterator j = ws.begin ();

    while (i != eow) { // 遍歷同一個 literal 底下的各個 watched clause

      const Watch w = *j++ = *i++; // 取完 watch 之後此時的 j 會指向存放 w 的 "下一個" 位置, 因此之後每次要回去找 w 的位置時都要下 j-1
      const signed char b = val (w.blit);

      if (b > 0) continue;                // blocking literal satisfied, 代表有其中一個 literal 是 true, 那整個 clause 就會是 true!

      if (w.binary ()) {

        // In principle we can ignore garbage binary clauses too, but that
        // would require to dereference the clause pointer all the time with
        //
        // if (w.clause->garbage) { j--; continue; } // (*)
        //
        // This is too costly.  It is however necessary to produce correct
        // proof traces if binary clauses are traced to be deleted ('d ...'
        // line) immediately as soon they are marked as garbage.  Actually
        // finding instances where this happens is pretty difficult (six
        // parallel fuzzing jobs in parallel took an hour), but it does
        // occur.  Our strategy to avoid generating incorrect proofs now is
        // to delay tracing the deletion of binary clauses marked as garbage
        // until they are really deleted from memory.  For large clauses
        // this is not necessary since we have to access the clause anyhow.
        //
        // Thanks go to Mathias Fleury, who wanted me to explain why the
        // line '(*)' above was in the code. Removing it actually really
        // improved running times and thus I tried to find concrete
        // instances where this happens (which I found), and then
        // implemented the described fix.

        // Binary clauses are treated separately since they do not require
        // to access the clause at all (only during conflict analysis, and
        // there also only to simplify the code). 他的意思應該是說, 因為 w.clause-> 的這個動作如果太頻繁的話會造成記憶體內容物太常置換, 進而降低效率, 再加上 binary clause 的處理只需要下面兩行 code 即可完成, 也不需要動用到 clause 裡面的 data, 那我何不直接保留那些 garbage clause, 還能節省掉 w.clause-> 和 j-- 的時間?

        if (b < 0) conflict = w.clause;          // but continue ... 我們知道 w.blit 並不等於 lit, 因為 binary clause 的處理只會在這個區段, 而這邊沒有 assign blocking literal 的 code, 可想而知它們的 blit 只會在 void watch_clause (Clause * c) in line 426 of internal.hpp 設定, 看一下那邊的 code 就知道了。既然 w.blit 不等於 lit, 那這兩個 literal 就都是 false 了, 但為什麼不直接 break 呢???
        else search_assign (w.blit, w.clause); // 這一行一定是 b == 0 (blocking literal unassigned), 因為 line 170 已經把 b > 0 的情況擋掉了, 所以就讓 blocking literal 變成 true 吧!

      } else { // 從這邊開始就不是 binary clause 了

        if (conflict) break; // Stop if there was a binary conflict already. (應是同一個 literal 裡面在之前已經先看過其他 clause 所造成)

        // The cache line with the clause data is forced to be loaded here
        // and thus this first memory access below is the real hot-spot of
        // the solver.  Note, that this check is positive very rarely and
        // thus branch prediction should be almost perfect here. 而且下面的 if 不常走進去, 所以 branch prediction 見效???

        if (w.clause->garbage) { j--; continue; } // 如果這個子句已經被丟掉的話, 當然就繼續看下一個

        literal_iterator lits = w.clause->begin ();

        // Simplify code by forcing 'lit' to be the second literal in the
        // clause.  This goes back to MiniSAT.  We use a branch-less version
        // for conditionally swapping the first two literals, since it
        // turned out to be substantially faster than this one
        //
        //  if (lits[0] == lit) swap (lits[0], lits[1]); 作者希望把現在正在看的 literal 調到第二個位置。注意到我們正在觀察的 lit 一定會是 lits[0] 或 lits[1] 其中一個, 這從 void watch_clause (Clause * c) in line 426 of internal.hpp 也可以知道。
        //
        // which achieves the same effect, but needs a branch.
        //
        const int other = lits[0]^lits[1]^lit;
        lits[0] = other, lits[1] = lit; /* 這一行很重要... 此時 lits[1] 必為 false */

        const signed char u = val (other); // value of the other watch

        if (u > 0) j[-1].blit = other; // satisfied, just replace blit, 並繼續往下一個 watch 邁進
        else { // 此時第 1 個 literal (lits[0]) 不是 false 就是 unassigned, 而我想要 eagerly 地把自己 (lits[1]) 這個 false watched literal 和後面的 non-false unwatched literal 調換, 所以剛開始一大段都是在做這件事。

          // This follows Ian Gent's (JAIR'13) idea of saving the position
          // of the last watch replacement.  In essence it needs two copies
          // of the default search for a watch replacement (in essence the
          // code in the 'if (v < 0) { ... }' block below), one starting at
          // the saved position until the end of the clause and then if that
          // one failed to find a replacement another one starting at the
          // first non-watched literal until the saved position.

          const int size = w.clause->size;
          const literal_iterator middle = lits + w.clause->pos;
          const const_literal_iterator end = lits + size;
          literal_iterator k = middle;

          // Find replacement watch 'r' at position 'k' with value 'v'.

          int r = 0; // 這個初始值有必要嗎? 當一開始就 k == end 的時候需要?
          signed char v = -1; // 這個初始值有必要嗎? 當一開始就 k == end 的時候需要?

          while (k != end && (v = val (r = *k)) < 0)
            k++; // k 從前一次儲存點 middle 開始往後走到下一個 non-false literal, 如果自己本身符合條件的話就不用移動, 此時把變數名稱記錄給 r, 變數值記錄給 v

          if (v < 0) {  // need second search starting at the head? 如果從 middle 開始到最後面都沒找到的話 (也就是這一段通通都是 false)

            k = lits + 2; // 就再重新從第 3 個 literal 開始往後找
            assert (w.clause->pos <= size);
            while (k != middle && (v = val (r = *k)) < 0)
              k++; // 如果還是找不到的話最後會回到一開始的 middle 點
          }

          w.clause->pos = k - lits;  // always save position, 重新記錄找到的新位置

          assert (lits + 2 <= k), assert (k <= w.clause->end ());

          if (v > 0) { // 如果找到的 unwatched literal 是 true, 我竟然也不用作 replacement, 直接設定 blocking literal 就好??? 這樣不會出問題嗎??

            // Replacement satisfied, so just replace 'blit'.

            j[-1].blit = r;

          } else if (!v) { // 如果找到的 unwatched literal 是 unassigned

            // Found new unassigned replacement literal to be watched.

            LOG (w.clause, "unwatch %d in", lit);

            lits[1] = r; // 這兩行其實是在作 swap, 原本的 lits[1] 是 lit (false), 而 *k 是 r (unassigned since !v),
            *k = lit; // 現在我們把 unassigned 的那個換進 lits[1], 而 false 的那個換出去到 *k
            watch_literal (r, lit, w.clause); // 更換 watched literal 之後 watch list 也要跟著更新, blocking literal 因為只是為了加快速度, 可以隨便抓, 不一定要是 true

            j--;  // Drop this watch from the watch list of 'lit'. 這句話是跟著上面那一行 watch list change 的。

          } else if (!u) { // 如果找不到 non-false unwatched literal, 且只剩第 1 個 literal 是 unassigned

            assert (v < 0); // 因為 v >= 0 的狀況在 line 265 到 line 282 已經被處理掉了, 所以這一塊的意思就是浮動指標 k 從第 3 個 literal 開始往後搜尋的過程中所看到的 literal 通通都是 false, 而第 2 個 literal 因為其反向在 trail 裡面所以也是 false, 那剩下的結論就如同 line 283 所說...

            // The other watch is unassigned ('!u') and all other literals
            // assigned to false (still 'v < 0'), thus we found a unit.
            // 這兩行英文其實就是在解釋我在上面幾行所寫的註解
            search_assign (other, w.clause); // other 根據 line 225 可以知道是第 1 個 literal 的意思

            // Similar code is in the implementation of the SAT'18 paper on
            // chronological backtracking but in our experience, this code
            // first does not really seem to be necessary for correctness,
            // and further does not improve running time either.
            //
            if (opts.chrono > 1) { // 為什麼要 > 1? 是因為上面那段註解說沒什麼用嗎? 那我就先不看囉

              const int other_level = var (other).level;

              if (other_level > var (lit).level) {

                // The assignment level of the new unit 'other' is larger
                // than the assignment level of 'lit'.  Thus we should find
                // another literal in the clause at that higher assignment
                // level and watch that instead of 'lit'.

                assert (size > 2);
                assert (lits[0] == other);
                assert (lits[1] == lit);

                int pos, s = 0;

                for (pos = 2; pos < size; pos++)
                  if (var (s = lits[pos]).level == other_level)
                    break;

                assert (s);
                assert (pos < size);

                LOG (w.clause, "unwatch %d in", lit);
                lits[pos] = lit;
                lits[1] = s;
                watch_literal (s, other, w.clause);

                j--;  // Drop this watch from the watch list of 'lit'.
              }
            }
          } else { // 如果找不到 non-false unwatched literal, 且連第 1 個 literal 都是 false

            assert (u < 0); // 因為 u > 0 的情況在 line 229 已經被處理掉了, 而 u == 0 則是在 line 283, 那剩下的情況當然就是 u < 0 囉
            assert (v < 0);

            // The other watch is assigned false ('u < 0') and all other
            // literals as well (still 'v < 0'), thus we found a conflict.

            conflict = w.clause;
            break; // 停止遍歷這個 literal 底下的 watch
          }
        }
      }
    }

    if (j != i) {

      while (i != eow)
        *j++ = *i++;

      ws.resize (j - ws.begin ());
    }
  } // 而如果已經找到 conflicting clause 了, 就也會順便跳出整個大迴圈, 停止遍歷 trail 裡其他剩下的 literal

  if (searching_lucky_phases) {

    if (conflict)
      LOG (conflict, "ignoring lucky conflict");

  } else { // 目前還看不出這些統計變數以及 no_conflict_until 會用在哪, 就先不理它們

    // Avoid updating stats eagerly in the hot-spot of the solver.
    //
    stats.propagations.search += propagated - before;

    if (!conflict) no_conflict_until = propagated;
    else {

      if (stable) stats.stabconflicts++;
      stats.conflicts++;

      LOG (conflict, "conflict");

      // The trail before the current decision level was conflict free.
      //
      no_conflict_until = control[level].trail;
    }
  }

  STOP (propagate);

  return !conflict;
}

}
