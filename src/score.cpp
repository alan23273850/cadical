#include "internal.hpp"

namespace CaDiCaL {

// This initializes variables on the binary 'scores' heap also with
// smallest variable index first (thus picked first) and larger indices at
// the end.
// 目前還沒看出來為什麼 smallest variable index first 和 larger indices at the end
void Internal::init_scores (int old_max_var, int new_max_var) { // only used in line 157 of internal.cpp
  LOG ("initializing EVSIDS scores from %d to %d",
    old_max_var + 1, new_max_var);
  for (int i = old_max_var + 1; i <= new_max_var; i++)
    scores.push_back (i);
}

// Shuffle the EVSIDS heap.

void Internal::shuffle_scores () { // only used in line 225 of rephase.cpp
  if (!opts.shuffle) return;
  if (!opts.shufflescores) return;
  assert (!level);
  stats.shuffled++;
  LOG ("shuffling scores");
  vector<int> shuffle;
  if (opts.shufflerandom){ // 想隨機
    scores.erase ();
    for (int idx = max_var; idx; idx--)
      shuffle.push_back (idx); // 先依序塞入 max_var, max_var-1, ..., 2, 1
    Random random (opts.seed);                  // global seed
    random += stats.shuffled;                   // different every time
    for (int i = 0; i <= max_var-2; i++) {
      const int j = random.pick_int (i, max_var-1);
      swap (shuffle[i], shuffle[j]); // 每次交換 shuffle 這個 vector 之中的任意兩個元素
    }
  } else { // 不想隨機，那就按照 heap 原本的順序, 從分數高的抓到分數低的
    while (!scores.empty ()) {
      int idx = scores.front ();
      (void) scores.pop_front ();
      shuffle.push_back (idx);
    }
  }
  scinc = 0;
  for (const auto & idx : shuffle) { // 此時 shuffle 已經按照我們想要的順序裝滿了原本 heap 的元素
    stab[idx] = scinc++; // 直接修改每個變數的 score, 而且分數要由 0 開始遞增
    scores.push_back (idx);  // 按照 shuffle 的順序依序推入 heap, 所以說如果不隨機的話其實就只是把原本 heap 元素的分數比序反轉而已。
  }
}

}
