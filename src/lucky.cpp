#include "internal.hpp"

namespace CaDiCaL {

// It turns out that even in the competition there are formulas which are
// easy to satisfy by either setting all variables to the same truth value
// or by assigning variables to the same value and propagating it.  In the
// latter situation this can be done either in the order of all variables
// (forward or backward) or in the order of all clauses.  These lucky
// assignments can be tested initially in a kind of pre-solving step.

int Internal::trivially_false_satisfiable () {
  LOG ("checking that all clauses contain a negative literal"); // ==> all "not-yet-satisfied" clauses contain an "unassigned" negative literal
  assert (!level); // (LOG) 這樣的話一定可以把那些 negative literal 都設成 true, 讓整個 formula satisfiable
  assert (assumptions.empty ());
  for (const auto & c : clauses) {
    if (c->garbage) continue;
    if (c->redundant) continue;
    bool satisfied = false, found_negative_literal = false;
    for (const auto & lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) { satisfied = true; break; } // 當下的 clause 已被一個 literal enable 成 true, 跳到下一個 clause
      if (tmp < 0) continue; // 若該 literal 已被賦值成 false, 則對整個 clause 無功用 (是 negative literal 也無法)
      if (lit > 0) continue; // 是 positive literal, 不符要找的條件
      found_negative_literal = true; // 最後留下來的這個 literal 就是我們要找的 "unassigned negative literal"
      break; // 一個 clause 只要一個 negative literal 即可
    }
    if (satisfied || found_negative_literal) continue; // 若這個子句已滿足, 或未滿足但有 negative literal, 則是我們要的, 繼續找下一個, 要全部的子句都這樣才行
    LOG (c, "found purely positively"); // 否則就是有一個 undetermined clause 都是 positive literals, 它：
    return 0; // 不符合這個 lucky condition, 繼續檢查下一個 lucky condition
  }
  VERBOSE (1, "all clauses contain a negative literal");
  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx)) continue; // 只考慮那些 unassigned literal
    search_assume_decision (-idx); // 沒仔細 trace, 但我猜是把 idx 號的 literal 設成 false
    if (propagate ()) continue; // 沒有 conflict 則繼續 decide 下一個變數, 不懂點：這個函式之所以要檢查 false literal, 不就是希望可以直接 assign 讓整個 formula 滿足嗎, 為什麼又要 propagate, 又可能會有 conflict?
    assert (level > 0);
    LOG ("propagation failed including redundant clauses"); // why redundant clauses? 不懂
    backtrack (); // 有 conflict 則需要 backtrack (unroll) 到之前狀態
    conflict = 0;
    return 0; // 所以只要遇到一次 conflict 就得放棄了嗎? (或許必須一次到位才能稱作 lucky phase 吧)
  }
  stats.lucky.constant.zero++;
  return 10; // 所有變數都設完仍然沒有 conflict, 代表我們找到一組解
}

int Internal::trivially_true_satisfiable () {
  LOG ("checking that all clauses contain a positive literal");
  assert (!level);
  assert (assumptions.empty ());
  for (const auto & c : clauses) {
    if (c->garbage) continue;
    if (c->redundant) continue;
    bool satisfied = false, found_positive_literal = false;
    for (const auto & lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) { satisfied = true; break; }
      if (tmp < 0) continue;
      if (lit < 0) continue;
      found_positive_literal = true;
      break;
    }
    if (satisfied || found_positive_literal) continue;
    LOG (c, "found purely negatively");
    return 0;
  }
  VERBOSE (1, "all clauses contain a positive literal");
  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx)) continue;
    search_assume_decision (idx);
    if (propagate ()) continue;
    assert (level > 0);
    LOG ("propagation failed including redundant clauses");
    backtrack ();
    conflict = 0;
    return 0;
  }
  stats.lucky.constant.one++;
  return 10;
}

/*------------------------------------------------------------------------*/

int Internal::forward_false_satisfiable () {
  LOG ("checking increasing variable index false assignment");
  assert (!unsat); // (LOG) 這邊又比第一個函式 trivially_false_satisfiable 更簡單, 不檢查每個 clause 有沒有 negative literal, 直接來
  assert (!level);
  assert (assumptions.empty ());
  int res = 0; // 下面 line 90-100 其實和上面的 line 33-42 是同一件事！
  for (int idx = 1; !res && idx <= max_var; idx++) {
    if (val (idx)) continue;
    search_assume_decision (-idx);
    if (!propagate ()) res = 20;
  }
  if (res) {
    assert (level > 0);
    backtrack ();
    conflict = 0;
    return 0;
  }
  VERBOSE (1, "forward assuming variables false satisfies formula");
  assert (satisfied ()); // 為什麼前面兩個函式不作這個檢查, 可是這裡就要？
  stats.lucky.forward.zero++;
  return 10;
}

int Internal::forward_true_satisfiable () {
  LOG ("checking increasing variable index true assignment");
  assert (!unsat);
  assert (!level);
  assert (assumptions.empty ());
  int res = 0;
  for (int idx = 1; !res && idx <= max_var; idx++) {
    if (val (idx)) continue;
    search_assume_decision (idx);
    if (!propagate ()) res = 20;
  }
  if (res) {
    assert (level > 0);
    backtrack ();
    conflict = 0;
    return 0;
  }
  VERBOSE (1, "forward assuming variables true satisfies formula");
  assert (satisfied ());
  stats.lucky.forward.one++;
  return 10;
}

/*------------------------------------------------------------------------*/

int Internal::backward_false_satisfiable () {
  LOG ("checking decreasing variable index false assignment");
  assert (!unsat);
  assert (!level);
  assert (assumptions.empty ());
  int res = 0;
  for (int idx = max_var; !res && idx > 0; idx--) {
    if (val (idx)) continue;
    search_assume_decision (-idx);
    if (!propagate ()) res = 20;
  }
  if (res) {
    assert (level > 0);
    backtrack ();
    conflict = 0;
    return 0;
  }
  VERBOSE (1, "backward assuming variables false satisfies formula");
  assert (satisfied ());
  stats.lucky.backward.zero++;
  return 10;
}

int Internal::backward_true_satisfiable () {
  LOG ("checking decreasing variable index true assignment");
  assert (!unsat);
  assert (!level);
  assert (assumptions.empty ());
  int res = 0;
  for (int idx = max_var; !res && idx > 0; idx--) {
    if (val (idx)) continue;
    search_assume_decision (idx);
    if (!propagate ()) res = 20;
  }
  if (res) {
    assert (level > 0);
    backtrack ();
    conflict = 0;
    return 0;
  }
  VERBOSE (1, "backward assuming variables true satisfies formula");
  assert (satisfied ());
  stats.lucky.backward.one++;
  return 10;
}

/*------------------------------------------------------------------------*/

// The following two functions test if the formula is a satisfiable horn
// formula.  Actually the test is slightly more general.  It goes over all
// clauses and assigns the first positive literal to true and propagates.
// Already satisfied clauses are of course skipped.  A reverse function
// is not implemented yet. Note: A Horn clause is a clause with at most one positive literal, called the head of the clause, and any number of negative literals, forming the body of the clause. (from https://en.wikipedia.org/wiki/Horn-satisfiability)

int Internal::positive_horn_satisfiable () {
  LOG ("checking that all clauses are positive horn satisfiable");
  assert (!level);
  assert (assumptions.empty ());
  for (const auto & c : clauses) {
    if (c->garbage) continue;
    if (c->redundant) continue;
    int positive_literal = 0;
    bool satisfied = false;
    for (const auto & lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) { satisfied = true; break; }
      if (tmp < 0) continue;
      if (lit < 0) continue;
      positive_literal = lit;
      break;
    }
    if (satisfied) continue;
    if (!positive_literal) {
      if (level > 0) backtrack ();
      LOG (c, "no positive unassigned literal in");
      assert (!conflict);
      return 0;
    } // 上半段旨在確保當下這個 clause, 若還沒滿足, 必須有至少一個 unassigned positive literal
    assert (positive_literal > 0);
    LOG (c, "found positive literal %d in", positive_literal);
    search_assume_decision (positive_literal); // 直接設定該 literal 為 true
    if (propagate ()) continue; // 一樣作 BCP 看看有沒有 conflict
    LOG ("propagation of positive literal %d leads to conflict",
      positive_literal);
    assert (level > 0);
    backtrack ();
    conflict = 0;
    return 0; // 一樣一旦遇有 conflict 就直接跳掉
  }
  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx)) continue;
    search_assume_decision (-idx); // 對剩下還沒 assign 的 literal 統一設成 false
    if (propagate ()) continue;
    LOG ("propagation of remaining literal %d leads to conflict", -idx);
    assert (level > 0);
    backtrack ();
    conflict = 0;
    return 0; // 一樣一旦遇有 conflict 就直接跳掉, but why, 一旦確定每個還沒滿足的 clause 都有 unassigned positive literal, 不是應該直接有 sat?
  }
  VERBOSE (1, "clauses are positive horn satisfied");
  assert (!conflict);
  assert (satisfied ());
  stats.lucky.horn.positive++;
  return 10;
}

int Internal::negative_horn_satisfiable () {
  LOG ("checking that all clauses are negative horn satisfiable");
  assert (!level);
  assert (assumptions.empty ());
  for (const auto & c : clauses) {
    if (c->garbage) continue;
    if (c->redundant) continue;
    int negative_literal = 0;
    bool satisfied = false;
    for (const auto & lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) { satisfied = true; break; }
      if (tmp < 0) continue;
      if (lit > 0) continue;
      negative_literal = lit;
      break;
    }
    if (satisfied) continue;
    if (!negative_literal) {
      if (level > 0) backtrack ();
      LOG (c, "no negative unassigned literal in");
      assert (!conflict);
      return 0;
    }
    assert (negative_literal < 0);
    LOG (c, "found negative literal %d in", negative_literal);
    search_assume_decision (negative_literal);
    if (propagate ()) continue;
    LOG ("propagation of negative literal %d leads to conflict",
      negative_literal);
    assert (level > 0);
    backtrack ();
    conflict = 0;
    return 0;
  }
  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx)) continue;
    search_assume_decision (idx);
    if (propagate ()) continue;
    LOG ("propagation of remaining literal %d leads to conflict", idx);
    assert (level > 0);
    backtrack ();
    conflict = 0;
    return 0;
  }
  VERBOSE (1, "clauses are negative horn satisfied");
  assert (!conflict);
  assert (satisfied ());
  stats.lucky.horn.negative++;
  return 10;
}

/*------------------------------------------------------------------------*/

int Internal::lucky_phases () {
  assert (!level);
  require_mode (SEARCH);
  if (!opts.lucky) return 0;

  // TODO: Some of the lucky assignments can also be found if there are
  // assumptions, but this is not completely implemented nor tested yet.
  //
  if (!assumptions.empty ()) return 0;

  START (search);
  START (lucky);
  assert (!searching_lucky_phases);
  searching_lucky_phases = true;
  stats.lucky.tried++; // the following 8 functions are the only ones defined and used in this file.
  int res       = trivially_false_satisfiable (); // 如果還沒 sat 的 clause 都有 unassigned negative literal, 都把它們設為 false 即可
  if (!res) res = trivially_true_satisfiable (); // 如果還沒 sat 的 clause 都有 unassigned positive literal, 都把它們設為 true 即可
  if (!res) res = forward_true_satisfiable (); // 對還沒 assign 的 literal 由小到大, 依序設成 true 去 BCP 看有沒有中, 如果在其中一個 literal 卡關, 就直接槓掉。
  if (!res) res = forward_false_satisfiable (); // 對還沒 assign 的 literal 由小到大, 依序設成 false 去 BCP 看有沒有中, 如果在其中一個 literal 卡關, 就直接槓掉。
  if (!res) res = backward_false_satisfiable (); // 對還沒 assign 的 literal 由大到小, 依序設成 false 去 BCP 看有沒有中, 如果在其中一個 literal 卡關, 就直接槓掉。
  if (!res) res = backward_true_satisfiable (); // 對還沒 assign 的 literal 由大到小, 依序設成 true 去 BCP 看有沒有中, 如果在其中一個 literal 卡關, 就直接槓掉。
  if (!res) res = positive_horn_satisfiable (); // 如果還沒 sat 的 clause 都有 unassigned positive literal, 都把它們設為 true, 其他還沒設定的 literal 統一設成 false, 就可以了嗎?
  if (!res) res = negative_horn_satisfiable (); // 如果還沒 sat 的 clause 都有 unassigned negative literal, 都把它們設為 false, 其他還沒設定的 literal 統一設成 true, 就可以了嗎?
  if (res == 10) stats.lucky.succeeded++;
  report ('l', !res);
  assert (searching_lucky_phases);
  searching_lucky_phases = false;
  STOP (lucky);
  STOP (search);
  return res;
}

}

// 目前最大的問題: 許多函式都再次作多餘的 BCP 和 conflict 檢查, 問題是那些前提條件不是就是因為滿足了之後就很好做才稱為 lucky phase 嗎?
// 或許我可以試著把那些 code 拿掉, 重新編譯, 拿一些測資試試看會不會對?
