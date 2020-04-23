#include "internal.hpp"

namespace CaDiCaL {

void Internal::init_watches () {
  assert (wtab.empty ());
  while (wtab.size () < 2*vsize) // 兩倍是因為要考慮正負兩種情況, 只是你想想看根據 vlit (lit) 計算 index 的方式其實應該是從 2 開始, 難道不用多 push 幾個 element 嗎?
    wtab.push_back (Watches ());
  LOG ("initialized watcher tables");
}

void Internal::clear_watches () { // 把每個 literal 各自所擁有的 watch list 通通清空
  for (int idx = 1; idx <= max_var; idx++)
    for (int sign = -1; sign <= 1; sign += 2)
      watches (sign * idx).clear ();
}

void Internal::reset_watches () { // 把整個 solver 全部的 watch list 都收回來
  assert (!wtab.empty ());
  erase_vector (wtab);
  LOG ("reset watcher tables");
}

// This can be quite costly since lots of memory is accessed in a rather
// random fashion, and thus we optionally profile it.

void Internal::connect_watches (bool irredundant_only) {
  START (connect);
  assert (watching ());

  LOG ("watching all %sclauses", irredundant_only ? "irredundant " : "");

  // First connect binary clauses.
  //
  for (const auto & c : clauses) {
    if (irredundant_only && c->redundant) continue;
    if (c->garbage || c->size > 2) continue;
    watch_clause (c); // line 426 of internal.hpp
  }

  // Then connect non-binary clauses.
  //
  for (const auto & c : clauses) {
    if (irredundant_only && c->redundant) continue;
    if (c->garbage || c->size == 2) continue;
    watch_clause (c); // line 426 of internal.hpp
    if (!level) { // 只有 level == 0 才要進來, 應該是種 implication 吧?
      const int lit0 = c->literals[0];
      const int lit1 = c->literals[1];
      const signed char tmp0 = val (lit0);
      const signed char tmp1 = val (lit1);
      if (tmp0 > 0) continue; // 一旦這個 literal 會讓整個 clause 變成 true 就不用看了
      if (tmp1 > 0) continue; // 一旦這個 literal 會讓整個 clause 變成 true 就不用看了
      if (tmp0 < 0) { // WHY???
        const size_t pos0 = var (lit0).trail;
        if (pos0 < propagated) {
          propagated = pos0;
          LOG ("literal %d resets propagated to %zd", lit0, pos0);
        }
      }
      if (tmp1 < 0) { // WHY???
        const size_t pos1 = var (lit1).trail;
        if (pos1 < propagated) {
          propagated = pos1;
          LOG ("literal %d resets propagated to %zd", lit1, pos1);
        }
      }
    }
  }

  STOP (connect);
}

void Internal::sort_watches () { // 每個 literal 都是先 binary clause 再 non-binary clause, 而 literal 的順序為 -1, 1, -2, 2, ... 依此類推。
  assert (watching ());
  LOG ("sorting watches");
  Watches saved;
  for (int idx = 1; idx <= max_var; idx++) {
    for (int sign = -1; sign <= 1; sign += 2) {

      const int lit = sign * idx;
      Watches & ws = watches (lit);

      const const_watch_iterator end = ws.end ();
      watch_iterator j = ws.begin ();
      const_watch_iterator i;

      assert (saved.empty ());

      for (i = j; i != end; i++) {
        const Watch w = *i;
        if (w.binary ()) *j++ = w;
        else saved.push_back (w);
      }
      ws.resize (j - ws.begin ());

      for (const auto & w : saved)
        ws.push_back (w); // 這邊我很好奇 STL vector 沒有 concatenate 的標準函式嗎?

      saved.clear ();
    }
  }
}

void Internal::disconnect_watches () { // 內容和 clear_watches 一模一樣...
  LOG ("disconnecting watches");
  for (int idx = 1; idx <= max_var; idx++)
    for (int sign = -1; sign <= 1; sign += 2)
      watches (sign * idx).clear ();
}

}
