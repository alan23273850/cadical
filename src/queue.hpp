#ifndef _queue_hpp_INCLUDED
#define _queue_hpp_INCLUDED

namespace CaDiCaL {

// Links for double linked decision queue.

struct Link {

  int prev, next;    // variable indices

  // initialized explicitly in 'init_queue' in queue.cpp
};

typedef vector<Link> Links;

// Variable move to front (VMTF) decision queue ordered by 'bumped'.  See
// our SAT'15 paper for an explanation on how this works.

struct Queue {

  // We use integers instead of variable pointers.  This is more compact and
  // also avoids issues due to moving the variable table during 'resize'.

  int first, last;    // anchors (head/tail) for doubly linked list
  int unassigned;     // all variables after this one are assigned, 我們只保證這個變數 "不會左於" 最右邊一個 unassigned 的變數 (但它可能指到比它還要右邊已經 assigned 的變數)
  int64_t bumped;     // see 'Internal.update_queue_unassigned', 記錄上面那個 unassigned 的變數當初被 enqueue 時的 timestamp (可以直接看成它在 queue 裡面的 position)
  // 所以上面兩個變數其實根本可以看成一個 pair!!! (重要)
  Queue () : first (0), last (0), unassigned (0), bumped (0) { }

  // We explicitly provide the mapping of integer indices to links to the
  // following two (inlined) functions.  This avoids including
  // 'internal.hpp' and breaks a cyclic dependency, so we can keep their
  // code here in this header file.  Otherwise they are just ordinary doubly
  // linked list 'dequeue' and 'enqueue' operations.
  // 只要把握住 links[idx].prev 代表第 idx 號 literal 的前方 literal 之序號；links[idx].next 代表後方 literal 之序號的定義即可！
  inline void dequeue (Links & links, int idx) { // 單純把 element 從 queue 裡面抓出來, 然後再把 queue 裡面的破損的地方修補起來
    Link & l = links[idx];
    if (l.prev) links[l.prev].next = l.next; else first = l.next;
    if (l.next) links[l.next].prev = l.prev; else last = l.prev;
  }

  inline void enqueue (Links & links, int idx) { // 單純把 element 接到 queue 的最尾端 (last)
    Link & l = links[idx];
    if ((l.prev = last)) links[last].next = idx; else first = idx;
    last = idx;
    l.next = 0;
  }
};

}

#endif
