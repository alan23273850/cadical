#include "internal.hpp"

namespace CaDiCaL {

// This function determines the next decision variable on the queue, without
// actually removing it from the decision queue, e.g., calling it multiple
// times without any assignment will return the same result.  This is of
// course used below in 'decide' but also in 'reuse_trail' to determine the
// largest decision level to backtrack to during 'restart' without changing
// the assigned variables (if 'opts.restartreusetrail' is non-zero).

int Internal::next_decision_variable_on_queue () {
  int64_t searched = 0;
  int res = queue.unassigned; // 從那個有名的 next-search 指標開始查找
  while (val (res)) // 往左邊持續搜尋直到找到 unassigned 的變數
    res = link (res).prev, searched++;
  if (searched) { // 如果指標確實有往前 (但我不太確定這個 guard 是否真有必要, 尤其是對於 update_queue_unassigned 而言, 是基於效率考量嗎?)
    stats.searched += searched;
    update_queue_unassigned (res); // 因為 res 快要變成 assigned 了, 所以要把 next-search 指標向左移至 res 以增進效率, 這也是當初指標設立的初衷。
  }
  LOG ("next queue decision variable %d bumped %" PRId64 "", res, bumped (res));
  return res;
}

// This function determines the best decision with respect to score.
// 很簡單, 持續檢查 heap 的 top (best) element 是不是還沒被 assign, 如果還沒那它當然可以成為我們的候選人, 如果已經 assign 的話就只能拿掉繼續檢查下一個了。
int Internal::next_decision_variable_with_best_score () {
  int res = 0;
  for (;;) {
    res = scores.front ();
    if (!val (res)) break;
    (void) scores.pop_front ();
  }
  LOG ("next decision variable %d with score %g", res, score (res));
  return res;
}

int Internal::next_decision_variable () { // 選出下一個 decision variable, 依據當下的環境可以走 VMTF 或 EVSIDS 兩種模式。
  if (use_scores ()) return next_decision_variable_with_best_score ();
  else               return next_decision_variable_on_queue ();
}

/*------------------------------------------------------------------------*/

// Implements phase saving as well using a target phase during
// stabilization unless decision phase is forced to the initial value.

int Internal::decide_phase (int idx, bool target) {
  const int initial_phase = opts.phase ? 1 : -1;
  int phase = 0;
  if (force_saved_phase) phase = phases.saved[idx];
  if (!phase && opts.forcephase) phase = initial_phase;
  if (!phase && target)  phase = phases.target[idx];
  if (!phase) phase = phases.saved[idx];
  if (!phase) phase = initial_phase;
  return phase * idx;
}

// The likely phase of an variable used in 'collect' for optimizing
// co-location of clauses likely accessed together during search.

int Internal::likely_phase (int idx) { return decide_phase (idx, false); }

/*------------------------------------------------------------------------*/

bool Internal::satisfied () {
  size_t assigned = trail.size ();
  if (propagated < assigned) return false;
  if ((size_t) level < assumptions.size ()) return false;
  return (assigned == (size_t) max_var);
}

// Search for the next decision and assign it to the saved phase.  Requires
// that not all variables are assigned.

int Internal::decide () {
  assert (!satisfied ());
  START (decide);
  int res = 0;
  if ((size_t) level < assumptions.size ()) { // 如果還有一些假設是 true 的變數還沒用到
    const int lit = assumptions[level]; // 取出之
    assert (assumed (lit));
    const signed char tmp = val (lit);
    if (tmp < 0) {
      LOG ("assumption %d falsified", lit);
      failing ();
      res = 20;
    } else if (tmp > 0) {
      LOG ("assumption %d already satisfied", lit);
      level++;
      control.push_back (Level (0, trail.size ()));
      LOG ("added pseudo decision level");
    } else {
      LOG ("deciding assumption %d", lit);
      search_assume_decision (lit);
    }
  } else { // 如果已經沒有預先假設的變數了
    stats.decisions++;
    int idx = next_decision_variable (); // 找出下一個要決定的變數
    const bool target = opts.stabilizephase && stable;
    int decision = decide_phase (idx, target);
    search_assume_decision (decision);
  }
  STOP (decide);
  return res;
}

}
