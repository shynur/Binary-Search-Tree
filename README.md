*if you just hope to use a map a little different from `std::map` but are not interested in how to implement it, please see **Declarations**; <br>or you might want to implement a binary search tree using this pattern, see **Details**; <br>there are also some tests that compared my implementations with `std::map`, see **Tests**.* <br>

`BST.hpp` 包含一个二叉搜索树的基类 `BST`, 可以用它简单实现一个平凡的二叉搜索树 `Plain`; 以及三颗平衡二叉搜索树 (继承自 `BST`), 分别是 AVL 树 `AVL`, Splay 树 `Spay`, 红黑树 `RedBlack`; 

**利用 `BST` 可以很简单地写出一个新的树结构而无需考虑过多的面向对象的问题, 将 `Plain` 的实现复制粘贴一遍, 再把名字 "Plain" 替换成你喜欢的. 最后专注于编写 `insert` 和 `erase` 两个方法即可.**

________________

## Declarations

### member variables

- **size**

- **root**: a node entity, which method search always start from

### methods

- **height**: what you only need to know is that one single node's height equals to 0

  ```C++
  AVL<int, int> t1{}, t2{};
  t2.insert(0, 0);
  assert(t1.height() == 0), assert(t2.height() == 1);
  ```
  
- **op<=>**: just compare WHATEVER you want! (comparison results follow the lexicographical in-order)

  ```C++
  AVL<int, int> avl{}; Splay<unsigned, unsigned> spl{};
  avl.insert(1, 3), avl.insert(0, 0); // {0-0, 1-3,}
  spl.insert(5, 2);                   // {5-2,}
  assert(avl <= spl); 
  // ie {0, 3} <= {2}
  ```

- **size, contains, begin, end, lower_bound, upper_bound, find, insert, erase... **: see `std::map`

- **constructors**: 

  ```C++
  AVL<int, int> avl{};
  Splay spl{avl};              // Splay<int, int>
  spl = AVL<unsigned, long>{}; 
  
  struct {int n; string s;} arr[] {{0, "zero"}, {1, "one"}, ...};
  RedBlack<int, string> rb{arr};
  // rb: {0-"zero", 1-"one", ...}
  
  rb = static_cast<map<int, n>>(rb);
  // no change
  
  // there are some other methods of initialize a BST, try yourself
  ```

- **destructor**: you can invoke a same `BST`'s destructor many times

### Node (some concepts)

- **internal**

  a internal node has key-value pair and left and right child

- **external**

  NOT have key-value pair; pointers to left and right child are `nullptr`

  height === 0, color ===BLACK

- **leaf**

  an internal node with two external children

____________

## Details

the following are the most important things you must be aware of, if you plan to write a `BST` yourself

- **zig** and **zag**

  if you never heard of these two words, go studying your CS curriculum;

  *zig* will return the reference of the node that occupy another node's position, where "another node" was at before zigging;

  ```C++
  a, b; // here are two nodes, and a is b's left child
  if (b.is_root()) 
      assert(&b == &b.zig());
      // b is a root fixed in a BST, so Node::zig will change somes nodes' topology and values
  else
      assert(&a == &b.zig());
      // b is NOT a root, so only need to change some nodes' topology, ie pointers
  ```

- i am lazy and tried now, and i don't want to write anymore.

  to see template class `Plain`'s implementation to understand the following things are enough
  
  - `Node::operator=`
  
  - `Node::swap`
  
  - `Node::~Node`
  
  - `Node::insert`
  
  - `Node::del`
  
  - `Node::p_next`
  
  - `BST::search`
  

________

## Tests

you can see these tests in file `test_bst.cpp`.

`std::map` 的性能在数据规模较小的时候, 大概是 `AVL` 的 1.1 ~ 1.4 倍, 其它树结构估计也差不多是这个水平. 但是在数据规模很大的时候 (如 9000, 0000), 运气好的话 `BST.hpp` 里的某些实现会比 `std::map` 更快.

测试用例大概长这样:

> ```C++
> for (unsigned i{0}; i != 1'0000'0000; ++i)
>     t.insert(i, ...);
> 
> assert(t.size() == 1'0000'0000);
> 
> for (unsigned i{1'0000'0000}; i-- != 0; )
>     t.find(i);
> for (unsigned i{0}; i != 1'0000'0000; ++i)
>     t.erase(i);
> 
> assert(t.size() == 0);
> ```

测试结果 `gcc 10.3 c++2a Ofast`

![标准库啊标准库, 你太让我失望啦~ 🤡](./.README/test_result.jpg)
