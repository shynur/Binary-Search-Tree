#include ".\BST.hpp"
using bst_Shynur::AVL;
using bst_Shynur::Splay;
using bst_Shynur::RedBlack;
#include <map>
#include <chrono>
#include <iomanip>
#include <iostream>
using namespace std;
// *INDENT-OFF*
constexpr struct {template<typename F>auto operator=(const F& f) const noexcept {auto start{chrono::steady_clock::now()}; const_cast<F&>(f)(); auto end{chrono::steady_clock::now()}; return chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();}} bench;
unsigned long long avl_insert{0}, avl_find{0}, avl_erase{0},
                   spl_insert{0}, spl_find{0}, spl_erase{0},
                   rb_insert{0},  rb_find{0},  rb_erase{0},
                   map_insert{0}, map_find{0}, map_erase{0};
constexpr unsigned n{1'0000'0000};
// *INDENT-ON*
int main() noexcept {
    //---------------------------------------------------------------------- AVL
    AVL<unsigned, bool> avl{};

    for (unsigned i{0}; i != n; ++i)
        avl_insert += bench = [&] {avl.insert(i, false);};

    for (unsigned i{n}; i-- != 0; )
        avl_find += bench = [&] {avl.find(i);};

    for (unsigned i{0}; i != n; ++i)
        avl_erase += bench = [&] {avl.erase(i);};

    //-------------------------------------------------------------------- Splay
    Splay<unsigned, bool> spl{};

    for (unsigned i{0}; i != n; ++i)
        spl_insert += bench = [&] {spl.insert(i, false);};

    for (unsigned i{n}; i-- != 0; )
        spl_find += bench = [&] {spl.find(i);};

    for (unsigned i{0}; i != n; ++i)
        spl_erase += bench = [&] {spl.erase(i);};

    //----------------------------------------------------------------- RedBlack
    RedBlack<unsigned, bool> rb{};

    for (unsigned i{0}; i != n; ++i)
        rb_insert += bench = [&] {rb.insert(i, false);};

    for (unsigned i{n}; i-- != 0; )
        rb_find += bench = [&] {rb.find(i);};

    for (unsigned i{0}; i != n; ++i)
        rb_erase += bench = [&] {rb.erase(i);};

    //----------------------------------------------------------------- std::map
    map<unsigned, bool> mp{};

    for (unsigned i{0}; i != n; ++i)
        map_insert += bench = [&] {mp.insert({i, false});};

    for (unsigned i{n}; i-- != 0; )
        map_find += bench = [&] {mp.find(i);};

    for (unsigned i{0}; i != n; ++i)
        map_erase += bench = [&] {mp.erase(i);};

    //--------------------------------------------------------------------------
    cerr << "size: " << n << endl
         << "time consumption (s):\n"
         << "     AVL  insertion: " << setw(10) << avl_insert / 1'000'000'000.0 << "  finding: " << setw(10) << avl_find / 1'000'000'000.0 << "  erasion: " << setw(10) << avl_erase / 1'000'000'000.0 << endl
         << "   Splay  insertion: " << setw(10) << spl_insert / 1'000'000'000.0 << "  finding: " << setw(10) << spl_find / 1'000'000'000.0 << "  erasion: " << setw(10) << spl_erase / 1'000'000'000.0 << endl
         << "RedBlack  insertion: " << setw(10) << rb_insert / 1'000'000'000.0 << "  finding: " << setw(10) << rb_find / 1'000'000'000.0 << "  erasion: " << setw(10) << rb_erase / 1'000'000'000.0 << endl
         << "std::map  insertion: " << setw(10) << map_insert / 1'000'000'000.0 << "  finding: " << setw(10) << map_find / 1'000'000'000.0 << "  erasion: " << setw(10) << map_erase / 1'000'000'000.0 << endl;
}
