#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// As in our original SATeLite published at SAT'05 we are trying to find
// gates in order to restrict the number of resolutions that need to be
// tried.  If there is such a gate, we only need to consider resolvents
// among gate and one non-gate clauses.  Resolvents between definitions will
// be tautological anyhow and resolvents among non-gates can actually be
// shown to be redundant too.

/*------------------------------------------------------------------------*/

// The next function returns a non-zero if the clause 'c', which is assumed
// to contain the literal 'first', after removing falsified literals is a
// binary clause.  Then the actual second literal is returned.

int
Internal::second_literal_in_binary_clause (Eliminator & eliminator,
                                           Clause * c, int first)
{
  assert (!c->garbage);
  int second = 0;
  for (const auto & lit : *c) {
    if (lit == first) continue;
    const signed char tmp = val (lit);
    if (tmp < 0) continue; // 就只是一個 falsified literal 而已
    if (tmp > 0) { // 因為已經被我發現整個 clause 結果是 true 了, 因此這個 clause 可以丟掉了
      mark_garbage (c);
      elim_update_removed_clause (eliminator, c);
      return 0; // 那 second literal 是啥其實也不重要了...
    }
    if (second) { second = INT_MIN; break; } // 超過一個 second literal, 那這個 clause 不符合假設阿
    second = lit; // 暫且找到我們要的 second literal 了
  }
  if (!second) return 0; // 如果 second literal 一個都沒有..
  if (second == INT_MIN) return 0; // 如果超過一個 second literal..
  assert (active (second)); // 沒意外的話應該要是還可以操作的
#ifdef LOGGING
  if (c->size == 2) LOG (c, "found binary");
  else LOG (c, "found actual binary %d %d", first, second);
#endif
  return second; // 回傳 second literal
}

/*------------------------------------------------------------------------*/

// Mark all other literals in binary clauses with 'first'.  During this
// marking we might also detect hyper unary resolvents producing a unit.
// If such a unit is found we propagate it and return immediately.

void Internal::mark_binary_literals (Eliminator & eliminator, int first) {

  if (unsat) return;
  if (val (first)) return;
  if (!eliminator.gates.empty ()) return;

  assert (!marked (first));
  assert (eliminator.marked.empty ());

  const Occs & os = occs (first);
  for (const auto & c : os) { // c 必定包含 first 這個 literal
    if (c->garbage) continue;
    const int second =
      second_literal_in_binary_clause (eliminator, c, first); // line 21
    if (!second) continue; // 如果這個 clause 沒有第二個 literal 就丟掉ㄅ
    const int tmp = marked (second); // 檢查看看是否已經在前幾次的迭代中先行遇過
    if (tmp < 0) { // 之前已經先遇過 {first,second}, 現在又遇到 {first,-second}, 一起做 resolution 得到 (first) 這個 unit literal!
      LOG ("found binary resolved unit %d", first);
      assign_unit (first); // 既然得到 unit literal, 就要直接設成 true 並 propagate 下去
      elim_propagate (eliminator, first);
      return; // 既然 first 已經是 true 了, 那剩下那些有包含 first 的子句都可以丟掉了, 直接跳出函式
    }
    if (tmp > 0) { // 之前已經先遇過 {first,second}, 現在又遇到一樣的 {first,second}, 這便是 duplicated clause!
      LOG (c, "duplicated actual binary clause");
      elim_update_removed_clause (eliminator, c);
      mark_garbage (c); // 把多餘的 clause 丟棄
      continue; // 繼續尋找下一個子句
    }
    eliminator.marked.push_back (second);
    mark (second); // 如果真有遇到 "還沒標記過 (tmp==0)" 的 second literal 的話, 就標記起來
    LOG ("marked second literal %d in binary clause %d %d",
      second, first, second);
  } // 注意從頭到尾只有 second 被標記起來, first 完全沒有被動到
}

// Unmark all literals saved on the 'marked' stack.

void Internal::unmark_binary_literals (Eliminator & eliminator) {
  LOG ("unmarking %zd literals", eliminator.marked.size ());
  for (const auto & lit : eliminator.marked)
    unmark (lit);
  eliminator.marked.clear ();
}

/*------------------------------------------------------------------------*/

// Find equivalence for 'pivot'.  Requires that all other literals in binary
// clauses with 'pivot' are marked (through 'mark_binary_literals');
// {-pivot, -x}, {pivot, x} <==> pivot = -x
void Internal::find_equivalence (Eliminator & eliminator, int pivot) {

  if (!opts.elimequivs) return;

  assert (opts.elimsubst);

  if (unsat) return;
  if (val (pivot)) return;
  if (!eliminator.gates.empty ()) return;

  mark_binary_literals (eliminator, pivot); // 把所有形如 {pivot, x} 之子句的 x 都標記起來
  if (unsat || val (pivot)) goto DONE;

  for (const auto & c : occs (-pivot)) {

    if (c->garbage) continue;

    const int second = // 找出形如 {-pivot, second} 的子句
      second_literal_in_binary_clause (eliminator, c, -pivot);
    if (!second) continue;
    const int tmp = marked (second);
    if (tmp > 0) { // 如果 second 標記和 x 一樣都是正的, 代表我們找到一組 {-pivot, second} = {-pivot, x} 子句, 那這句話就可以和前面的 {pivot, x} 一起做 resolution 得到 unit clause {x}
      LOG ("found binary resolved unit %d", second);
      assign_unit (second); // unit clause 必須進行 propagation
      elim_propagate (eliminator, second);
      if (val (pivot)) break; // 如果 pivot 已經有值的話, 那另外一個 equivalent literal 的值也是給定的, 這靠 propagation 便可直接完成, 因此直接跳出迴圈, 不用再繼續找 gate 了
      if (unsat) break;
    }
    if (tmp >= 0) continue; // 如果 second 標記和 x 相反號的話, 代表我們找到一組 {-pivot, second} = {-pivot, -x} 子句, 而 (pivot ∨ x) ∧ (-pivot ∨ -x) 要是 true 的充要條件便是 pivot = -x

    LOG ("found equivalence %d = %d", pivot, -second); // 所以 pivot = -x = second, LOG 最後一個參數 -second 應為作者筆誤
    stats.elimequivs++;
    stats.elimgates++;

    LOG (c, "first gate clause"); // 所以找到第一個 gate clause: c = {-pivot, -x}
    assert (!c->gate);
    c->gate = true;
    eliminator.gates.push_back (c);

    Clause * d = 0;
    const Occs & ps = occs (pivot);
    for (const auto & e : ps) {
      if (e->garbage) continue;
      const int other =
        second_literal_in_binary_clause (eliminator, e, pivot);
      if (other == -second) { d = e; break; } // c = {-pivot, -x} 的成對子句為 d = {pivot, x}, 我們還沒把它標記起來
    }
    assert (d);

    LOG (d, "second gate clause"); // 終於找到 d = {pivot, x} 可以標記了
    assert (!d->gate);
    d->gate = true;
    eliminator.gates.push_back (d);

    break;
  }

DONE:
  unmark_binary_literals (eliminator);
}

/*------------------------------------------------------------------------*/

// Find and gates for 'pivot' with a long clause, in which the pivot occurs
// positively.  Requires that all other literals in binary clauses with
// 'pivot' are marked (through 'mark_binary_literals');
// {-pivot, -x, -y, -z, ...}, {pivot, x}, {pivot, y}, {pivot, z}, ... <==> -pivot = (x ∧ y ∧ z ∧ ...)
void Internal::find_and_gate (Eliminator & eliminator, int pivot) {

  if (!opts.elimands) return;

  assert (opts.elimsubst);

  if (unsat) return;
  if (val (pivot)) return;
  if (!eliminator.gates.empty ()) return;

  mark_binary_literals (eliminator, pivot); // line 54, 把所有形如 {pivot, lit} 的子句的 lit 給標記起來
  if (unsat || val (pivot)) goto DONE;

  for (const auto & c : occs (-pivot)) { // 把包含 -pivot 的子句挑出來, 預期找到一個結構為 {-pivot, -x, -y, -z, ...} 的子句 c

    if (c->garbage) continue;
    if (c->size < 3) continue; // 確保 c 的 size >= 3, 因為一個 AND gate 至少需要 2 個 input, 所以長度不得小於 {-pivot, -x, -y}

    bool all_literals_marked = true;
    unsigned arity = 0; // 計算 c = {-pivot, -v, ...} 裡面的 -v 有 "確實出現在" 形如 {pivot, v} (於 line 180 被檢查) 之子句的個數
    for (const auto & lit : *c) { // 注意在此迴圈 lit 就相當於 -v, 有差一個 sign 所以看的時候要小心
      if (lit == -pivot) continue;
      assert (lit != pivot); // 因為 c 是從 occs(-pivot) 挑出來的, 就不可能再包含 pivot 了
      signed char tmp = val (lit);
      if (tmp < 0) continue; // 排除掉 falsified literals
      assert (!tmp); // 所以 lit 還沒被 assign
      tmp = marked (lit); // 檢查 line 180 的標記狀況
      if (tmp < 0) { arity++; continue; } // 若 -v 確實有出現在 {pivot, v} 裡面, 那這個 literal 合法, 繼續檢查下一個
      all_literals_marked = false; // 一旦很不幸地有一種 -v 無法出現在已經在 line 180 被檢查過的 {pivot, v} 裡面的話, c 就不能算是 gate clause
      break;
    }

    if (!all_literals_marked) continue; // 這個 clause 失敗了, 繼續尋找下一個 gate clause

#ifdef LOGGING
    if (opts.log) {
      Logger::print_log_prefix (this);
      tout.magenta ();
      printf ("found arity %u AND gate %d = ", arity, -pivot);
      bool first = true;
      for (const auto & lit : *c) {
        if (lit == -pivot) continue;
        assert (lit != pivot);
        if (!first) fputs (" & ", stdout);
        printf ("%d", -lit);
        first = false;
      }
      fputc ('\n', stdout);
      tout.normal ();
      fflush (stdout);
    }
#endif
    stats.elimands++;
    stats.elimgates++;

    (void) arity;
    assert (!c->gate);
    c->gate = true;
    eliminator.gates.push_back (c);
    for (const auto & lit : *c) { // 所以此時的 c = {-pivot, -x, -y, -z, ...}
      if (lit == -pivot) continue;
      assert (lit != pivot); // 因為 c 是從 occs(-pivot) 挑出來的, 就不可能再包含 pivot 了
      signed char tmp = val (lit);
      if (tmp < 0) continue; // 排除掉 falsified literals
      assert (!tmp); // 所以 lit 還沒被 assign
      assert (marked (lit) < 0); // 這是我們之前篩選的結果
      marks [vidx (lit)] *= 2; // 把 "有出現在 c" 的 other literals (-x, -y, -z, ...) 的標記都 * 2 以利識別, 等一下會用到
    }

    unsigned count = 0; // 計算所有包含 pivot 的 binary clause 之中可以和給定的目標子句 c = {-pivot, -x, -y, -z, ...} 配對的個數
    for (const auto & d : occs (pivot)) { // 把包含 pivot 的子句挑出來, 預期找到一個結構為 {pivot, v} 的子句 d
      if (d->garbage) continue;
      const int other =
        second_literal_in_binary_clause (eliminator, d, pivot);
      if (!other) continue; // 確認是 binary clause 且有 second literal
      const int tmp = marked (other);
      if (tmp != 2) continue; // 檢查看看這個 other (v) 是不是因為 -other (-v) 出現在 c 裡面而早就在上一段被標示過了, 如果是的話它才能和我們的 c 配對!
      LOG (d, "AND gate binary side clause");
      assert (!d->gate);
      d->gate = true;
      eliminator.gates.push_back (d);
      count++;
    }
    assert (count >= arity); // 這很正常, 本來就應該要正確 (更精確地來說是相等), 但, 為什麼要特地設計兩個 counter 就只為了做 assertion 呢?
    (void) count;

    break; // 我只要找到一組 gate 就好
  }

DONE:
  unmark_binary_literals (eliminator); // 前面的標記是為了讓結構 {pivot, a} 和子句 {-pivot, -a, -b, -c, ...} 作配對用, 函式結束之後務必復原, 否則會干擾到其他函式作業!
}

/*------------------------------------------------------------------------*/

// Find and extract ternary clauses. (把 d 中還沒 assign 的 literal 存進 a, b, c 裡, 唯有確實是 ternary 時才回傳 true)

bool Internal::get_ternary_clause (Clause * d, int & a, int & b, int & c)
{
  if (d->garbage) return false;
  if (d->size < 3) return false;
  int found = 0;
  a = b = c = 0;
  for (const auto & lit : *d) {
    if (val (lit)) continue; // 略過已賦值的 literal
       if (++found == 1) a = lit;
    else if (found == 2) b = lit;
    else if (found == 3) c = lit;
    else return false;
  }
  return found == 3;
}

// This function checks whether 'd' exists as ternary clause or as a binary
// clause subsuming 'd' (contains only the given literals). 看不出來有後者的功能呢...?

bool Internal::match_ternary_clause (Clause * d, int a, int b, int c) {
  if (d->garbage) return false;
  int found = 0;
  for (const auto & lit : *d) {
    if (val (lit)) continue; // 略過已賦值的 literal
    if (a != lit && b != lit && c != lit) return false;
    found++;
  }
  return found == 3;
}

Clause * // 找找看有沒有 literal 恰好為 a, b, c 的 ternary clause, 有的話回傳其指標, 否則是空指標
Internal::find_ternary_clause (int a, int b, int c) {
  if (occs (b).size () > occs (c).size ()) swap (b, c);
  if (occs (a).size () > occs (b).size ()) swap (a, b);
  for (auto d : occs (a))
    if (match_ternary_clause (d, a, b, c))
      return d;
  return 0;
}

/*------------------------------------------------------------------------*/

// Find if-then-else gate.

void Internal::find_if_then_else (Eliminator & eliminator, int pivot) {

  if (!opts.elimites) return;

  assert (opts.elimsubst);

  if (unsat) return;
  if (val (pivot)) return;
  if (!eliminator.gates.empty ()) return;

  const Occs & os = occs (pivot);
  const auto end = os.end ();
  for (auto i = os.begin (); i != end; i++) {
    Clause * di = *i;
    int ai, bi, ci;
    if (!get_ternary_clause (di, ai, bi, ci)) continue;
    if (bi == pivot) swap (ai, bi);
    if (ci == pivot) swap (ai, ci);
    assert (ai == pivot);
    for (auto j = i + 1; j != end; j++) {
      Clause * dj = *j;
      int aj, bj, cj;
      if (!get_ternary_clause (dj, aj, bj, cj)) continue;
      if (bj == pivot) swap (aj, bj);
      if (cj == pivot) swap (aj, cj);
      assert (aj == pivot);
      if (abs (bi) == abs (cj)) swap (bj, cj);
      if (abs (ci) == abs (cj)) continue;
      if (bi != -bj) continue;
      Clause * d1 = find_ternary_clause (-pivot, bi, -ci);
      if (!d1) continue;
      Clause * d2 = find_ternary_clause (-pivot, bj, -cj);
      if (!d2) continue;
      LOG (di, "1st if-then-else"); // di = {pivot, bi, ci}
      LOG (dj, "2nd if-then-else"); // dj = {pivot, -bi, cj}
      LOG (d1, "3rd if-then-else"); // d1 = {-pivot, bi, -ci}
      LOG (d2, "4th if-then-else"); // d2 = {-pivot, -bi, -cj}
      LOG ("found ITE gate %d == (%d ? %d : %d)", pivot, -bi, -ci, -cj); // 需要一點 equivalence gate 的概念才能理解
      assert (!di->gate);
      assert (!dj->gate);
      assert (!d1->gate);
      assert (!d2->gate);
      di->gate = true;
      dj->gate = true;
      d1->gate = true;
      d2->gate = true;
      eliminator.gates.push_back (di);
      eliminator.gates.push_back (dj);
      eliminator.gates.push_back (d1);
      eliminator.gates.push_back (d2);
      stats.elimgates++;
      stats.elimites++;
      return;
    }
  }
}

/*------------------------------------------------------------------------*/

// Find and extract clause. (把 c 之中未賦值的 lit 全部塞進 l 之中)

bool Internal::get_clause (Clause * c, vector<int> & l) {
  if (c->garbage) return false;
  l.clear ();
  for (const auto & lit : *c) {
    if (val (lit)) continue; // 已經賦值的 literal 就不要推了
    l.push_back (lit);
  }
  return true;
}

// Check whether 'c' contains only the literals in 'l'. (未賦值的部分要等價才會是 true)

bool Internal::is_clause (Clause * c, const vector<int> & lits) {
  if (c->garbage) return false;
  int size = lits.size ();
  if (c->size < size) return false;
  int found = 0;
  for (const auto & lit : *c) {
    if (val (lit)) continue; // 一樣忽視已經被賦值的 literal
    const auto it = find (lits.begin (), lits.end (), lit);
    if (it == lits.end ()) return false;
    if (++found > size) return false;
  }
  return found == size;
}

Clause * Internal::find_clause (const vector<int> & lits) {
  int best = 0;
  size_t len = 0;
  for (const auto & lit : lits) {
    size_t l = occs (lit).size ();
    if (best && l >= len) continue;
    len = l, best = lit;
  } // 此時 best 在所有 lits 之中有最短 occurrence list
  for (auto c : occs (best)) // 枚舉所有包含 best 的 clause
    if (is_clause (c, lits)) // 如果 lits 確實代表這個 clause, 就 ↓
      return c; // 回傳這個子句
  return 0; // 如果真的找不到則回傳空指標
}

void Internal::find_xor_gate (Eliminator & eliminator, int pivot) {

  if (!opts.elimxors) return;

  assert (opts.elimsubst);

  if (unsat) return;
  if (val (pivot)) return;
  if (!eliminator.gates.empty ()) return;

  vector<int> lits;

  for (auto d : occs (pivot)) { // 令 d 為一個包含 pivot 的子句 (不過有沒有包含 pivot 在 xor gate 之中並不是很重要)

    if (!get_clause (d, lits)) continue; // 如果子句是垃圾的話就不要, 否則把 d 的 literal 們通通推進 lits 這個 vector

    const int size = lits.size ();      // clause size
    const int arity = size - 1;         // arity of XOR

    if (size < 3) continue;
    if (arity > opts.elimxorlim) continue;

    assert (eliminator.gates.empty ());

    unsigned needed = (1u << arity) - 1;        // additional clauses, 還需要 2^arity - 1 個子句, 萬一 arity 超過 31 的話怎麼辦...?
    unsigned signs = 0;                         // literals to negate (初始值代表 d 子句的 encoding)

    do { // 這個迴圈把 signs 視為如 line 437 的註解所說, 是用 bit 去記錄哪些 literal 相對於一開始的 clause d 而言必須被翻過來, 我們可以發現到 signs 一開始等於 0, 這意味著 d 子句每個 literal 其實都對應到 0, 那麼當某個 bit 變成 1 的時候自然是那個位置對應到的 literal 要 negate 過來了!
      const unsigned prev = signs;
      while (parity (++signs)) // 從 prev 開始累加到二進位表示法 1 的個數為偶數為止, xor gate 最終會把從 0 開始到 2^size - 1 之間所有代表 even parity 的子句通通算進來, 原理我在本地端存有附件檔記錄
        ;
      for (int j = 0; j < size; j++) {
        const unsigned bit = 1u << j; // 萬一 j 超過 31 的話怎麼辦...?
        int lit = lits[j];
        if ((prev & bit) != (signs & bit)) // 如果 prev 和 signs 的第 j 個 bit 值並不同, 就 ↓
          lits[j] = lit = -lit; // 把第 j 個 literal 翻過來。為什麼不直接寫成 lits[j] = -lits[j] 呢? 我真的不懂。
      }
      Clause * e = find_clause (lits); // 希望找得到我們要的子句
      if (!e) break;
      eliminator.gates.push_back (e);
    } while (--needed); // 一旦找到數量足夠多的不重複子句, 就可以跳出來了, 因為我們已經找到一組 gate 了

    if (needed) { eliminator.gates.clear (); continue; } // 如果還有被需要的子句沒有找到, 這代表 d 無法勝任我們的 gate clause

    eliminator.gates.push_back (d);
    assert (eliminator.gates.size () == (1u << arity)); // 除了原本 needed 的數量之外, 還要加上 d 自己

#ifdef LOGGING
    if (opts.log) {
      Logger::print_log_prefix (this);
      tout.magenta ();
      printf ("found arity %u XOR gate %d = ", arity, -pivot);
      bool first = true;
      for (const auto & lit : *d) {
        if (lit == pivot) continue;
        assert (lit != -pivot);
        if (!first) fputs (" ^ ", stdout);
        printf ("%d", lit);
        first = false;
      }
      fputc ('\n', stdout);
      tout.normal ();
      fflush (stdout);
    }
#endif
    stats.elimgates++;
    stats.elimxors++;
    const auto end = eliminator.gates.end ();
    auto j = eliminator.gates.begin ();
    for (auto i = j; i != end; i++) { // 這個迴圈以及下面那一行都只是在從 eliminator.gates 這個 vector 之中篩選出還沒標上 gate 的 clause 並且幫它們標上, WHY?? 此外, 為什麼上半部在找子句的時候不直接順便 ->gate = true; 呢?
      Clause * e = *i;
      if (e->gate) continue;
      e->gate = true;
      LOG (e, "contributing");
      *j++ = e;
    }
    eliminator.gates.resize (j - eliminator.gates.begin ());

    break;
  }
}

/*------------------------------------------------------------------------*/

// Find a gate for 'pivot'.  If such a gate is found, the gate clauses are
// marked and pushed on the stack of gates.  Further hyper unary resolution
// might detect units, which are propagated.  This might assign the pivot or
// even produce the empty clause.

void Internal::find_gate_clauses (Eliminator & eliminator, int pivot)
{
  if (!opts.elimsubst) return;

  if (unsat) return;
  if (val (pivot)) return;

  assert (eliminator.gates.empty ());

  find_equivalence (eliminator, pivot);
  find_and_gate (eliminator, pivot);
  find_and_gate (eliminator, -pivot); // 不是很清楚為什麼 AND gate 就要分正負 pivot 兩種情況，其他 gate 就不用, 我猜應該是因為 AND gate 內部有分主從子句, 意即結構不對稱, 而其他 gate 是對稱的, 就只要試一次就好
  find_if_then_else (eliminator, pivot);
  find_xor_gate (eliminator, pivot);
}

void Internal::unmark_gate_clauses (Eliminator & eliminator) {
  LOG ("unmarking %zd gate clauses", eliminator.gates.size ());
  for (const auto & c : eliminator.gates) {
    assert (c->gate);
    c->gate = false;
  }
  eliminator.gates.clear ();
}

/*------------------------------------------------------------------------*/

}
