#include "internal.hpp"

namespace CaDiCaL {

// Slightly different than 'bump_variable' since the variable is not
// enqueued at all.
// 和 enqueue 在 queue.hpp 的差別 (special: ) 在於多了 opts.reverse 的分流、更新時間戳 btab[idx] 以及順便更新 next-search 指標 queue.unassigned 之位置。
inline void Internal::init_enqueue (int idx) { // only used in line 53
  Link & l = links[idx];
  if (opts.reverse) { // special: 如果我想把 element 插進 queue 前面?
    l.prev = 0;
    if (queue.first) {
      assert (!links[queue.first].prev);
      links[queue.first].prev = idx;
      btab[idx] = btab[queue.first] - 1; // special: 因為前面元素的 (虛擬) 時間戳必須較小, 方便的做法就是直接從後面的元素減 1 即可! 會不會有可能變成 0 呢? 這樣的話, 又合法嗎?
    } else {
      assert (!queue.last);
      queue.last = idx;
      btab[idx] = 0; // special: 只有我一個人, 時間戳設成 0 應該也沒關係?!
    }
    assert (btab[idx] <= stats.bumped); // 一個是減 1, 一個是直接設成 0, 這樣應該..對...吧?
    l.next = queue.first;
    queue.first = idx;
    if (!queue.unassigned) // special: 如果還沒設定 next-search 指針所指向的變數的話,
      update_queue_unassigned (queue.last); // 就直接讓它指向最後一個元素吧! 相反地, 如果 next-search 已有目標, 因為我們是左插新頂點, 根本不可能去更動到 next-search 右邊的元素屬性, 所以它指標的定義也不會被違背, 自然沒有更動指標的必要。
  } else { // 這部分 queue 的操作和 enqueue(links, idx) 應該相同, 為何不直接呼叫 function?
    l.next = 0;
    if (queue.last) {
      assert (!links[queue.last].next);
      links[queue.last].next = idx;
    } else {
      assert (!queue.first);
      queue.first = idx;
    }
    btab[idx] = ++stats.bumped; // special: 只要是 enqueue 就要更新時間戳
    l.prev = queue.last;
    queue.last = idx;
    update_queue_unassigned (queue.last); // special: 剛從尾端新加入的元素應該是 unassigned, 所以指標也必須跟著移到尾端, 就算不是 unassigned, 指標尾移的這個動作也不違反其定義
  }
}

// Initialize VMTF queue from current 'old_max_var + 1' to 'new_max_var'.
// This incorporates an initial variable order.  We currently simply assume
// that variables with smaller index are more important.  This is the same
// as in MiniSAT (implicitly) and also matches the 'scores' initialization.
//
void Internal::init_queue (int old_max_var, int new_max_var) { // only used in line 156 of internal.cpp
  LOG ("initializing VMTF queue from %d to %d",
    old_max_var + 1, new_max_var);
  assert (old_max_var < new_max_var);
  assert (!level);
  for (int idx = old_max_var; idx < new_max_var; idx++)
    init_enqueue (idx + 1); // 持續呼叫上面那個函式，從 'old_max_var + 1' 到 'new_max_var'
}

// Shuffle the VMTF queue.

void Internal::shuffle_queue () { // only used in line 226 of rephase.cpp
  if (!opts.shuffle) return;
  if (!opts.shufflequeue) return;
  stats.shuffled++;
  LOG ("shuffling queue");
  vector<int> shuffle;
  if (opts.shufflerandom) { // 想隨機
    for (int idx = max_var; idx; idx--)
      shuffle.push_back (idx); // 先依序塞入 max_var, max_var-1, ..., 2, 1
    Random random (opts.seed);                  // global seed
    random += stats.shuffled;                   // different every time
    for (int i = 0; i <= max_var-2; i++) {
      const int j = random.pick_int (i, max_var-1);
      swap (shuffle[i], shuffle[j]); // 每次交換 shuffle 這個 vector 之中的任意兩個元素
    }
  } else { // 不想隨機，那就按照 queue 原本的順序, 從最後一個推回第一個
    for (int idx = queue.last; idx; idx = links[idx].prev)
      shuffle.push_back (idx);
  }
  queue.first = queue.last = 0; // 清空整個 queue, 要特別注意的是根據其實作方式, 我們不需要連 links 這個 vector 一併清空, HEN 方便!!!
  for (const int idx : shuffle) // 此時 shuffle 已經按照我們想要的順序裝滿了原本 queue 的元素
    queue.enqueue (links, idx); // 按照 shuffle 的順序依序推入 queue, 所以說如果不隨機的話其實就只是把原本的 queue 反轉而已。
  int64_t bumped = queue.bumped; // 因為 line 83 把 next_assign 指標指向最後一個元素, 於是必須 btab[queue.last] = queue.bumped
  for (int idx = queue.last; idx; idx = links[idx].prev)
    btab[idx] = bumped--; // 讓愈後面的元素有愈高的時間戳, 因為我們已經對 queue 重新洗牌了, 這個時間戳就不一定要是真的, 只要能保持順序, 分得出來誰先誰後就可以了。
  queue.unassigned = queue.last; // 直接初始化 next_assign 指標到最後一個元素
}

}
