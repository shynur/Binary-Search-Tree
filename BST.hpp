/*
 * one pattern for generating BST and some popular implementations of BBST
 * Copyright (C) 2022 Shynur <one.last.kiss@qq.com>.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

#ifndef BST_Shynur
#define BST_Shynur
#define NDEBUG

// *INDENT-OFF*
#include <map>           // std::unordered_map <-> BST_T
#include <ranges>        // std::ranges::range
#include <cassert>       // debug: macro assert(expr...)
#include <cstddef>       // std::size_t, the result_type of std::hash::operator()
#include <cstdlib>       // std::abs
#include <utility>       // std::move, std::swap, std::pair, std::declval
#include <concepts>      // BST_T, trait bounds...
#include <algorithm>     // std::max
#include <exception>     // throw from operator[]
#include <functional>    // std::hash
#include <type_traits>   // std::remove_cvref_t
#include <unordered_map> // std::unordered_map <-> BST_T
namespace bst_Shynur {
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) struct BST {
        int size() const noexcept;
        int height() const noexcept;

        std::size_t hash() const noexcept;
        bool contains(const K& key) const noexcept;

        template<std::constructible_from<const K&> J, std::constructible_from<V&&> U>explicit operator std::map<J, U>() && noexcept;
        template<std::constructible_from<const K&> J, std::constructible_from<V&&> U>explicit operator std::multimap<J, U>() && noexcept;
        template<std::constructible_from<const K&> J, std::constructible_from<V&&> U>explicit operator std::unordered_map<J, U>() && noexcept;
        template<std::constructible_from<const K&> J, std::constructible_from<V&&> U>explicit operator std::unordered_multimap<J, U>() && noexcept;
        
        template<std::constructible_from<const K&> J, std::constructible_from<const V&> U>explicit operator std::map<J, U>() const& noexcept;
        template<std::constructible_from<const K&> J, std::constructible_from<const V&> U>explicit operator std::multimap<J, U>() const& noexcept;
        template<std::constructible_from<const K&> J, std::constructible_from<const V&> U>explicit operator std::unordered_map<J, U>() const& noexcept;
        template<std::constructible_from<const K&> J, std::constructible_from<const V&> U>explicit operator std::unordered_multimap<J, U>() const& noexcept;

        template<typename J, std::equality_comparable_with<V> U>bool operator==(const BST<J, U>& b) const noexcept;
        template<typename J, std::equality_comparable_with<V> U>bool operator!=(const BST<J, U>& b) const noexcept;
        template<typename J, std::totally_ordered_with<V> U>bool operator<(const BST<J, U>& b) const noexcept;
        template<typename J, std::totally_ordered_with<V> U>bool operator>(const BST<J, U>& b) const noexcept;
        template<typename J, std::totally_ordered_with<V> U>bool operator<=(const BST<J, U>& b) const noexcept;
        template<typename J, std::totally_ordered_with<V> U>bool operator>=(const BST<J, U>& b) const noexcept;

        V& operator[](const K& key) const;
        
        template<std::ranges::range map_T>BST& operator+=(map_T& b) noexcept requires(std::copy_constructible<V>);
        template<std::ranges::range map_T>requires(!std::is_const_v<map_T>) BST& operator+=(map_T&& _b) noexcept;

        virtual ~BST() noexcept;
    protected:
        unsigned size_{0};

        struct Node final {struct alignas(8) Entry final {const K key;
                                                          V val; 
                                                          [[nodiscard]] std::size_t hash() const noexcept;} *p{nullptr};
                           Node *p_parent, *p_left{nullptr}, *p_right{nullptr};
                           unsigned height{0};
                           enum: bool {RED = false, BLACK = true} color{BLACK};

                           Node(Node *const _p_parent) noexcept: p_parent{_p_parent} {}

                           // insert Entry at an [external] Node; dye this [red]
                           Node& insert(const K& key, V val) noexcept;

                           // remove an [internal] Node [with 0 or 1 internal child]
                           Node& del() noexcept;

                           [[nodiscard]] int get_height() const noexcept;

                           // call the following 2 functions only when this is an [internal] Node
                           [[nodiscard]] Node *p_prev() const noexcept;
                           [[nodiscard]] Node *p_next() const noexcept;

                           [[nodiscard]] bool internal() const noexcept;
                           [[nodiscard]] bool external() const noexcept;
                           [[nodiscard]] bool is_root() const noexcept;

                           // call it only when this is [internal]
                           [[nodiscard]] bool is_leaf() const noexcept;
                           [[nodiscard]] bool internal_left() const noexcept;
                           [[nodiscard]] bool internal_right() const noexcept;

                           // call the following 3 functions only when this is [NOT root]
                           [[nodiscard]] bool is_left() const noexcept;
                           [[nodiscard]] bool is_right() const noexcept;
                           [[nodiscard]] Node *& ptr_from_parent() const noexcept;

                           // the following 2 functions only update internal nodes
                           template<std::regular_invocable<Node&> updater_T>void update(const updater_T& updater) noexcept {assert(internal()); updater(*this);}
                           template<std::regular_invocable<Node&> updater_T>void update_backward(const updater_T& updater) noexcept {for (Node *p_cur_node{this}; p_cur_node; p_cur_node = p_cur_node->p_parent) [[likely]] updater(*p_cur_node);}

                           // methods zig and zag only do zigging and zagging; they will not update node's information;
                           Node& zig() noexcept;
                           Node& zag() noexcept;} mutable root{nullptr};

        [[nodiscard]] Node& search(const K& key) const noexcept;
    public:
        struct iterator final {bool operator==(const iterator& b) const noexcept;
                               bool operator!=(const iterator& b) const noexcept;

                               Node::Entry& operator*() const noexcept;
                               Node::Entry *operator->() const noexcept;

                               using difference_type = int;
                               iterator& operator++() noexcept;
                               iterator& operator--() noexcept;
                               iterator operator++(int) noexcept;
                               iterator operator--(int) noexcept;

                               iterator(const Node& node = {nullptr}): p_node{&node} {}
                               iterator(const iterator&) noexcept = default;
                           private:
                               const Node *p_node;
                               friend struct BST;};

        iterator begin() const noexcept;
        iterator end() const noexcept;

        iterator lower_bound(const K& key) const noexcept;
        iterator upper_bound(const K& key) const noexcept;
        
        iterator find(const K& key) const noexcept;

        virtual void insert(const K& key, V val) noexcept = 0;
        virtual void erase(const K& key) noexcept = 0;

        // do NOT invoke the following 2 functions, because they are written for Splay; any binary tree may be converted to a Splay
        [[nodiscard]] const Node& get_root_ref_for_Splay_() && noexcept;
        [[nodiscard]] const unsigned& get_size_ref_for_Splay_() && noexcept;
    protected:
        [[nodiscard]] static Node *iter2ptr(const iterator& iter) noexcept;
};  template<typename T>concept BST_T = (requires(const T bst) {bst.begin()->key, bst.begin()->val;}) && std::derived_from<std::remove_cvref_t<T>, BST<std::remove_cvref_t<decltype(std::declval<T>().begin()->key)>, std::remove_cvref_t<decltype(std::declval<T>().begin()->val)>>>;

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) class Plain final: public BST<K, V> {
        using BST<K, V>::root;
        using BST<K, V>::size_;

        static const constexpr auto height_updater{[](BST<K, V>::Node& node) noexcept {assert(node.internal()); node.height = 1 + std::max(node.p_left->height, node.p_right->height);}};
    public:
        Plain() noexcept = default;
        Plain(const Plain& b) noexcept requires(std::copy_constructible<V>): Plain{} {*this += b;}
        Plain(Plain&& _b) noexcept: Plain{} {swap(*this, _b);}
        friend void swap(Plain& a, Plain& b) noexcept {std::swap(a.size_, b.size_), std::swap(a.root, b.root); if (a.root.p_left) [[likely]] a.root.p_left->p_parent = &(a.root); if (a.root.p_right) [[likely]] a.root.p_right->p_parent = &(a.root); if (b.root.p_left) [[likely]] b.root.p_left->p_parent = &(b.root); if (b.root.p_right) [[likely]] b.root.p_right->p_parent = &(b.root);}
        Plain& operator=(Plain b) noexcept;

        template<std::ranges::range map_T>requires(!std::same_as<std::remove_cvref_t<map_T>, Plain>) Plain(map_T& b) noexcept requires(std::copy_constructible<V>): Plain{} {*this += b;}
        template<std::ranges::range map_T>requires(!std::same_as<std::remove_cvref_t<map_T>, Plain> && !std::is_const_v<map_T>) Plain(map_T&& _b) noexcept: Plain{} {*this += std::move(_b);}

        virtual void insert(const K& key, V val) noexcept override;
        virtual void erase(const K& key) noexcept override;
};  template<BST_T T>                                                                               Plain(T)                             -> Plain<std::remove_cvref_t<decltype(std::declval<T>().begin()->key)>, std::remove_cvref_t<decltype(std::declval<T>().begin()->val)>>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) Plain(std::map<K, V>)                -> Plain<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) Plain(std::multimap<K, V>)           -> Plain<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) Plain(std::unordered_map<K, V>)      -> Plain<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) Plain(std::unordered_multimap<K, V>) -> Plain<K, V>;

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) class AVL final: public BST<K, V> {
        using BST<K, V>::root;
        using BST<K, V>::size_;

        static const constexpr auto height_updater{[](BST<K, V>::Node& node) noexcept {assert(node.internal()); node.height = 1 + std::max(node.p_left->height, node.p_right->height);}};
    public:
        AVL() noexcept = default;
        AVL(const AVL& b) noexcept requires(std::copy_constructible<V>): AVL{} {*this += b;}
        AVL(AVL&& _b) noexcept: AVL{} {swap(*this, _b);}
        friend void swap(AVL& a, AVL& b) noexcept {std::swap(a.size_, b.size_), std::swap(a.root, b.root); if (a.root.p_left) [[likely]] a.root.p_left->p_parent = &(a.root); if (a.root.p_right) [[likely]] a.root.p_right->p_parent = &(a.root); if (b.root.p_left) [[likely]] b.root.p_left->p_parent = &(b.root); if (b.root.p_right) [[likely]] b.root.p_right->p_parent = &(b.root);}
        AVL& operator=(AVL b) noexcept;

        template<std::ranges::range map_T>requires(!std::same_as<std::remove_cvref_t<map_T>, AVL>) AVL(map_T& b) noexcept requires(std::copy_constructible<V>): AVL{} {*this += b;}
        template<std::ranges::range map_T>requires(!std::same_as<std::remove_cvref_t<map_T>, AVL> && !std::is_const_v<map_T>) AVL(map_T&& _b) noexcept: AVL{} {*this += std::move(_b);}

        virtual void insert(const K& key, V val) noexcept override;
        virtual void erase(const K& key) noexcept override;
};  template<BST_T T>                                                                               AVL(T)                             -> AVL<std::remove_cvref_t<decltype(std::declval<T>().begin()->key)>, std::remove_cvref_t<decltype(std::declval<T>().begin()->val)>>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) AVL(std::map<K, V>)                -> AVL<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) AVL(std::multimap<K, V>)           -> AVL<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) AVL(std::unordered_map<K, V>)      -> AVL<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) AVL(std::unordered_multimap<K, V>) -> AVL<K, V>;

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) class Splay final: public BST<K, V> {
        using BST<K, V>::root;
        using BST<K, V>::size_;
        int height() const noexcept = delete;

        // only splay an internal node
        static void splay(typename BST<K, V>::Node *const p_node) noexcept;
    public:
        Splay() noexcept = default;
        Splay(const Splay& b) noexcept requires(std::copy_constructible<V>): Splay{} {*this += b;}
        Splay(Splay&& _b) noexcept: Splay{} {swap(*this, _b);}
        friend void swap(Splay& a, Splay& b) noexcept {std::swap(a.size_, b.size_), std::swap(a.root, b.root); if (a.root.p_left) [[likely]] a.root.p_left->p_parent = &(a.root); if (a.root.p_right) [[likely]] a.root.p_right->p_parent = &(a.root); if (b.root.p_left) [[likely]] b.root.p_left->p_parent = &(b.root); if (b.root.p_right) [[likely]] b.root.p_right->p_parent = &(b.root);}
        Splay& operator=(Splay b) noexcept;

        template<std::ranges::range map_T>requires(!std::same_as<std::remove_cvref_t<map_T>, Splay>) Splay(map_T& b) noexcept requires(std::copy_constructible<V>): Splay{} {*this += b;}
        template<std::ranges::range map_T>requires(!std::same_as<std::remove_cvref_t<map_T>, Splay> && !std::is_const_v<map_T>) Splay(map_T&& _b) noexcept: Splay{} {if constexpr(!std::derived_from<std::remove_cvref_t<map_T>, BST<K, V>>) *this += std::move(_b); else {std::swap(size_, const_cast<unsigned&>(std::move(_b).get_size_ref_for_Splay_())), swap(root, const_cast<BST<K, V>::Node&>(std::move(_b).get_root_ref_for_Splay_())); if (root.p_left) [[likely]] root.p_left->p_parent = &(root); if (root.p_right) [[likely]] root.p_right->p_parent = &(root);}}

        virtual void insert(const K& key, V val) noexcept override;
        virtual void erase(const K& key) noexcept override;

        // Splay::find will invalidate iterator; it will also change this Splay's topology, so it is not a const method
        BST<K, V>::iterator find(const K& key) noexcept;
};  template<BST_T T>                                                                               Splay(T)                             -> Splay<std::remove_cvref_t<decltype(std::declval<T>().begin()->key)>, std::remove_cvref_t<decltype(std::declval<T>().begin()->val)>>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) Splay(std::map<K, V>)                -> Splay<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) Splay(std::multimap<K, V>)           -> Splay<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) Splay(std::unordered_map<K, V>)      -> Splay<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) Splay(std::unordered_multimap<K, V>) -> Splay<K, V>;

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) class RedBlack final: public BST<K, V> {
        using BST<K, V>::root;
        using BST<K, V>::size_;

        // solution to insertion does NOT include the situation when [p_node is a root], so need "root.color = BLACK" to be written in RedBlack::insert
        static void insertion_sln(BST<K, V>::Node *const p_node) noexcept;
        // assert that p_node is a [BLACK] node
        static void erasion_sln(BST<K, V>::Node *p_node) noexcept;
    public:
        RedBlack() noexcept = default;
        RedBlack(const RedBlack& b) noexcept requires(std::copy_constructible<V>): RedBlack{} {*this += b;}
        RedBlack(RedBlack&& _b) noexcept: RedBlack{} {swap(*this, _b);}
        friend void swap(RedBlack& a, RedBlack& b) noexcept {std::swap(a.size_, b.size_), std::swap(a.root, b.root); if (a.root.p_left) [[likely]] a.root.p_left->p_parent = &(a.root); if (a.root.p_right) [[likely]] a.root.p_right->p_parent = &(a.root); if (b.root.p_left) [[likely]] b.root.p_left->p_parent = &(b.root); if (b.root.p_right) [[likely]] b.root.p_right->p_parent = &(b.root);}
        RedBlack& operator=(RedBlack b) noexcept;

        template<std::ranges::range map_T>requires(!std::same_as<std::remove_cvref_t<map_T>, RedBlack>) RedBlack(map_T& b) noexcept requires(std::copy_constructible<V>): RedBlack{} {*this += b;}
        template<std::ranges::range map_T>requires(!std::same_as<std::remove_cvref_t<map_T>, RedBlack> && !std::is_const_v<map_T>) RedBlack(map_T&& _b) noexcept: RedBlack{} {*this += std::move(_b);}

        virtual void insert(const K& key, V val) noexcept override;
        virtual void erase(const K& key) noexcept override;

        int height() const noexcept;
};  template<BST_T T>                                                                               RedBlack(T)                             -> RedBlack<std::remove_cvref_t<decltype(std::declval<T>().begin()->key)>, std::remove_cvref_t<decltype(std::declval<T>().begin()->val)>>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) RedBlack(std::map<K, V>)                -> RedBlack<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) RedBlack(std::multimap<K, V>)           -> RedBlack<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) RedBlack(std::unordered_map<K, V>)      -> RedBlack<K, V>;
    template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) RedBlack(std::unordered_multimap<K, V>) -> RedBlack<K, V>;

} namespace std {template<::bst_Shynur::BST_T T>struct hash<T> {using argument_type = T; using result_type = size_t; result_type operator()(const argument_type& to_hash) const noexcept{return to_hash.hash();}};}
/*----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::RedBlack<K, V>::erase(const K& key) noexcept {

    if (typename BST<K, V>::Node *p_node{&BST<K, V>::search(key)}; p_node->internal()) {
        --size_;

        if (typename BST<K, V>::Node *p_next_node; p_node->internal_left() && p_node->internal_right())
            p_next_node = p_node->p_next(),
            std::swap(p_node->p, p_next_node->p),
            p_node = p_next_node;

        if (const bool color_of_erasion{p_node->color}; (p_node = &p_node->del())->color && color_of_erasion)
            erasion_sln(p_node);
        else
            p_node->color = BST<K, V>::Node::BLACK;
    }
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::RedBlack<K, V>::erasion_sln(typename BST<K, V>::Node *p_node) noexcept {
    
    assert(p_node->color);

    if (typename BST<K, V>::Node *const p_parent{p_node->p_parent}; p_parent) [[likely]] {
        const bool dir{p_node->is_right()};

        if (typename BST<K, V>::Node *const p_sibling{dir ? p_parent->p_left : p_parent->p_right}; p_sibling->color)
            if (const auto color_of_parent{p_parent->color}, color_of_left_nibling{p_sibling->p_left->color}, color_of_right_nibling{p_sibling->p_right->color}; color_of_left_nibling && color_of_right_nibling)
                if (p_sibling->color = BST<K, V>::Node::RED; color_of_parent)
                    erasion_sln(p_parent);
                else
                    p_parent->color = BST<K, V>::Node::BLACK;
            else {
                if (dir ? color_of_left_nibling : color_of_right_nibling) 
                    (dir ? p_sibling->zag() : p_sibling->zig()).color = color_of_parent;
                else
                    p_sibling->color = color_of_parent;

                p_node = &(dir ? p_parent->zig() : p_parent->zag()),
                p_node->p_left->color = p_node->p_right->color = BST<K, V>::Node::BLACK;
            }
        else
            (dir ? p_parent->zig() : p_parent->zag()).color = BST<K, V>::Node::BLACK,
            p_node->p_parent->color = BST<K, V>::Node::RED,
            erasion_sln(p_node);
    }
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::RedBlack<K, V>::insert(const K& key, V val) noexcept {

    if (typename BST<K, V>::Node& to_insert{BST<K, V>::search(key)}; to_insert.internal()) {
        using std::swap;
        swap(to_insert.p->val, val);
    } else
        insertion_sln(&to_insert.insert(key, std::move(val))),
        root.color = BST<K, V>::Node::BLACK,
        ++size_;
}

// solve the problem when the insertion leads to a [RED] node's child is also [RED] 
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::RedBlack<K, V>::insertion_sln(typename BST<K, V>::Node *const p_node) noexcept {

    if (typename BST<K, V>::Node *const p_parent{p_node->p_parent}; p_parent) [[likely]] 
        if (typename BST<K, V>::Node *p_grandparent{p_parent->p_parent}; !(p_parent->color || p_node->color)) {
            const bool dir{p_parent->is_right()};

            if (typename BST<K, V>::Node *const p_parsib{dir ? p_grandparent->p_left : p_grandparent->p_right}; p_parsib->color) {
                if (dir != p_node->is_right())
                    dir ? p_parent->zig() : p_parent->zag();
            
                (p_grandparent = &(dir ? p_grandparent->zag() : p_grandparent->zig()))->color = BST<K, V>::Node::BLACK,
                p_grandparent->p_left->color = p_grandparent->p_right->color = BST<K, V>::Node::RED;

            } else
                p_parsib->color = p_parent->color = BST<K, V>::Node::BLACK,
                p_grandparent->color = BST<K, V>::Node::RED,
                insertion_sln(p_grandparent);
        }
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
int
bst_Shynur::RedBlack<K, V>::height() const noexcept {

    unsigned black_height{0};

    for (const typename BST<K, V>::Node *p_node{&root}; p_node->internal(); p_node = p_node->p_left)
        if (p_node->color)
            ++black_height;

    return static_cast<int>(black_height);
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::RedBlack<K, V>&
bst_Shynur::RedBlack<K, V>::operator=(RedBlack b) noexcept {

    return swap(*this, b),
           *this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::iterator
bst_Shynur::Splay<K, V>::find(const K& key) noexcept {

    typename BST<K, V>::Node *p_searched{&BST<K, V>::search(key)}; 

    if (p_searched->internal())
        splay(p_searched), 
        p_searched = &root;
    else 
        if (size_) [[likely]]
            splay(p_searched->p_parent);

    return p_searched->internal() ? typename bst_Shynur::BST<K, V>::iterator{*p_searched} : BST<K, V>::end();
}

// ensure that p_node will point to an internal node or null after the block of if-else
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::Splay<K, V>::erase(const K& key) noexcept {

    typename BST<K, V>::Node *p_node{&BST<K ,V>::search(key)}; 

    if (p_node->internal()) {
        --size_;

        if (typename BST<K, V>::Node *p_next_node; p_node->internal_left() && p_node->internal_right())
            p_next_node = p_node->p_next(), 
            std::swap(p_node->p, p_next_node->p),
            p_node = p_next_node;
        
        p_node = p_node->del().p_parent;

    } else 
        p_node = p_node->p_parent;

    if (p_node && p_node->internal()) [[likely]]
        splay(p_node);
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::Splay<K, V>::insert(const K& key, V val) noexcept {

    typename BST<K, V>::Node& to_insert{BST<K ,V>::search(key)};

    if (to_insert.internal()) {
        using std::swap;
        swap(to_insert.p->val, val);
    } else
        to_insert.insert(key, std::move(val)), 
        ++size_;

    splay(&to_insert);
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::Splay<K, V>::splay(typename BST<K, V>::Node *const p_node) noexcept {

    assert(p_node->internal());

    if (typename BST<K, V>::Node *const p_parent{p_node->p_parent}, *p_grandparent; p_parent) [[likely]]
        if (const bool dir{p_node->is_right()}; p_grandparent = p_parent->p_parent) [[likely]]
            splay(
               &(
                    p_parent->is_right() == dir ?
                    (dir ? p_grandparent->zag().zag() : p_grandparent->zig().zig())
                    : (dir ? (p_parent->zag(), p_grandparent->zig()) : (p_parent->zig(), p_grandparent->zag()))
                )
            );
        else
            dir ? p_parent->zag() : p_parent->zig();
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::Plain<K, V>::insert(const K& key, V val) noexcept {

    if (typename BST<K, V>::Node& to_insert{BST<K ,V>::search(key)}; to_insert.internal()) {
        using std::swap;
        swap(to_insert.p->val, val);
    } else
        to_insert.insert(key, std::move(val)).update_backward(height_updater),
        ++size_;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::Plain<K, V>::erase(const K& key) noexcept {

    if (typename BST<K, V>::Node *p_to_erase{&BST<K ,V>::search(key)}; p_to_erase->internal()) {
        --size_;

        if (typename BST<K, V>::Node *p_next_node; p_to_erase->internal_left() && p_to_erase->internal_right())
            p_next_node = p_to_erase->p_next(), 
            std::swap(p_to_erase->p, p_next_node->p),
            p_to_erase = p_next_node;
        
        if (typename BST<K, V>::Node *p_parent{p_to_erase->del().p_parent}; p_parent) [[likely]]
            p_parent->update_backward(height_updater);
    }
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::Plain<K, V>&
bst_Shynur::Plain<K, V>::operator=(Plain b) noexcept {

    return swap(*this, b),
           *this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::Splay<K, V>&
bst_Shynur::Splay<K, V>::operator=(Splay b) noexcept {

    return swap(*this, b),
           *this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::AVL<K, V>::erase(const K& key) noexcept {

    if (typename BST<K, V>::Node *p_cur_node{&BST<K, V>::search(key)}; p_cur_node->internal()) {
        --size_;

        if (typename BST<K, V>::Node *p_next_node; p_cur_node->internal_left() && p_cur_node->internal_right())
            p_next_node = p_cur_node->p_next(), std::swap(p_cur_node->p, p_next_node->p), p_cur_node = p_next_node;
        
        for (p_cur_node = p_cur_node->del().p_parent; p_cur_node; p_cur_node = p_cur_node->p_parent) [[likely]]
            if (const int left_height{p_cur_node->p_left->get_height()}, right_height{p_cur_node->p_right->get_height()}; std::abs(left_height - right_height) <= 1)
                p_cur_node->height = 1 + std::max(left_height, right_height);
            else {
                const bool dir{left_height < right_height};

                if (typename BST<K, V>::Node& child{*(dir ? p_cur_node->p_right : p_cur_node->p_left)}; dir ? child.p_left->height > child.p_right->height : child.p_right->height > child.p_left->height)
                    dir ? child.zig() : child.zag();

                (p_cur_node = &(dir ? p_cur_node->zag() : p_cur_node->zig()))->p_left->update(height_updater),
                p_cur_node->p_right->update(height_updater),
                p_cur_node->update(height_updater);
            }
    }
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::AVL<K, V>&
bst_Shynur::AVL<K, V>::operator=(AVL b) noexcept {

    return swap(*this, b),
           *this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
void
bst_Shynur::AVL<K, V>::insert(const K& key, V val) noexcept {

    if (typename BST<K, V>::Node& to_insert{BST<K ,V>::search(key)}; to_insert.internal()) {
        using std::swap;
        swap(to_insert.p->val, val);
    } else
        for (typename BST<K, V>::Node *p_cur_node{(++size_, &to_insert.insert(key, std::move(val)))}; p_cur_node; p_cur_node = p_cur_node->p_parent) [[likely]]
            if (const int left_height{p_cur_node->p_left->get_height()}, right_height{p_cur_node->p_right->get_height()}; std::abs(left_height - right_height) <= 1)
                p_cur_node->height = 1 + std::max(left_height, right_height);
            else {
                const bool dir{left_height < right_height};

                if (typename BST<K, V>::Node& child{*(dir ? p_cur_node->p_right : p_cur_node->p_left)}; dir != (child.p_left->height < child.p_right->height))
                    dir ? child.zig() : child.zag();

                (p_cur_node = &(dir ? p_cur_node->zag() : p_cur_node->zig()))->p_left->update(height_updater),
                p_cur_node->p_right->update_backward(height_updater);

                break;
            }
}

// an external node's height is always 0
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
int
bst_Shynur::BST<K, V>::height() const noexcept {

    return root.get_height();
}

// if there is a key which and the given key are equal, return reference of an internal node;
// otherwise, return reference of an external node that means the given key is a new key; 
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
bst_Shynur::BST<K, V>::Node&
bst_Shynur::BST<K, V>::search(const K& key) const noexcept {

    for (typename BST<K, V>::Node *p_cur_node{&root}; ; p_cur_node = (key < p_cur_node->p->key ? p_cur_node->p_left : p_cur_node->p_right))
        if (p_cur_node->external() || p_cur_node->p->key == key)
            return *p_cur_node;
        else [[likely]]
            continue;
}

// boundary of the given iterator: [begin, end]
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::Node *
bst_Shynur::BST<K, V>::iter2ptr(const iterator& iter) noexcept {

    assert(iter.p_node != nullptr);

    return const_cast<Node *>(iter.p_node);
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<std::ranges::range map_T>
bst_Shynur::BST<K, V>&
bst_Shynur::BST<K, V>::operator+=(map_T& b) noexcept requires(std::copy_constructible<V>) {

    for (const auto& [key, val] : b)
        insert(key, val);

    return *this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<std::ranges::range map_T>requires(!std::is_const_v<map_T>)
bst_Shynur::BST<K, V>&
bst_Shynur::BST<K, V>::operator+=(map_T&& _b) noexcept {

    for (auto& [key, val] : _b)
        insert(key, std::move(val));

    return *this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
V&
bst_Shynur::BST<K, V>::operator[](const K& key) const {

    if (const iterator found{find(key)}; found != end())
        return found->val;
    else {
        static const constexpr struct: public std::exception {
            const char *const err_info_bst_Shynur{"`the key does NOT exist` from BST::operator[const K&]"};
            virtual const char *what() const noexcept override {
                return err_info_bst_Shynur;
            }
        } err{};
        throw err;
    }
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::iterator
bst_Shynur::BST<K, V>::find(const K& key) const noexcept {

    const Node& searched{search(key)};

    return searched.internal() ? iterator{searched} : end();
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::iterator
bst_Shynur::BST<K, V>::upper_bound(const K& key) const noexcept {

    iterator lower_iter{lower_bound(key)},
             end_iter{end()};

    assert(lower_iter == end() || lower_iter->key >= key);

    return lower_iter == end_iter ? end_iter : (lower_iter->key == key ? ++lower_iter : lower_iter);
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::iterator
bst_Shynur::BST<K, V>::lower_bound(const K& key) const noexcept {

    if (const Node& result{search(key)}; result.internal())
        return {result};
    else
        if (size_ == 0) [[unlikely]]
            return {root};
        else
            if (iterator parent_iter{*result.p_parent}; result.is_left())
                return parent_iter;
            else
                return ++parent_iter;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<typename J, std::totally_ordered_with<V> U>
bool
bst_Shynur::BST<K, V>::operator<(const BST<J, U>& b) const noexcept {

    auto b_iter{b.begin()}, b_end{b.end()};

    for (iterator a_iter{begin()}, a_end{end()}; a_iter != a_end && b_iter != b_end; ++a_iter, ++b_iter) [[likely]]
        if (a_iter->val == b_iter->val) [[likely]]
            continue;
        else
            return a_iter->val < b_iter->val;

    return size() < b.size();
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<typename J, std::equality_comparable_with<V> U>
bool
bst_Shynur::BST<K, V>::operator==(const BST<J, U>& b) const noexcept {

    if (size() != b.size()) [[likely]]
        return false;
    else
        for (auto b_iter{b.begin()}; const auto& [_, val] : *this)
            if ((b_iter++)->val != val) [[unlikely]]
                return false;

    return true;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<typename J, std::equality_comparable_with<V> U>inline
bool
bst_Shynur::BST<K, V>::operator!=(const BST<J, U>& b) const noexcept {

    return !(*this == b);
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<typename J, std::totally_ordered_with<V> U>inline
bool
bst_Shynur::BST<K, V>::operator>(const BST<J, U>& b) const noexcept {

    return b < *this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<typename J, std::totally_ordered_with<V> U>inline
bool
bst_Shynur::BST<K, V>::operator>=(const BST<J, U>& b) const noexcept {

    return b <= *this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<typename J, std::totally_ordered_with<V> U>inline
bool
bst_Shynur::BST<K, V>::operator<=(const BST<J, U>& b) const noexcept {

    return *this < b || *this == b;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
bst_Shynur::BST<K, V>::iterator
bst_Shynur::BST<K, V>::begin() const noexcept {

    if (size() == 0) [[unlikely]]
        return {root};
    else
        for (const Node *p_node{&root}; ; p_node = p_node->p_left)
            if (p_node->internal_left()) [[likely]]
                continue;
            else
                return {*p_node};
}

// an iterator at the end always points to an external node
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
bst_Shynur::BST<K, V>::iterator
bst_Shynur::BST<K, V>::end() const noexcept {

    for (const Node *p_node{&root}; ; p_node = p_node->p_right)
        if (p_node->internal()) [[likely]]
            continue;
        else
            return {*p_node};
}

// size === number of keys === number of internal nodes
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
int
bst_Shynur::BST<K, V>::size() const noexcept {

    return static_cast<int>(size_);
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
std::size_t
bst_Shynur::BST<K, V>::hash() const noexcept {

    std::size_t elem_hash_code{0};

    for (std::size_t x{1}; const auto& entry : *this)
        elem_hash_code += entry.hash() * x,
        x *= 3;

    return elem_hash_code ^ std::hash<int>{}(size());
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<std::constructible_from<const K&> J, std::constructible_from<const V&> U>
bst_Shynur::BST<K, V>::operator
std::map<J, U>() const& noexcept {

    std::map<J, U> m{};

    for (const auto& [k, v] : *this)
        m.insert(std::pair<J, U>{k, v});

    assert(m.size() == size());

    return m;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<std::constructible_from<const K&> J, std::constructible_from<V&&> U>
bst_Shynur::BST<K, V>::operator
std::map<J, U>() && noexcept {

    std::map<J, U> m{};

    for (auto& [k, v] : *this)
        m.insert(std::pair<J, U>{k, std::move(v)});

    assert(m.size() == size());

    return ~BST(),
           m;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<std::constructible_from<const K&> J, std::constructible_from<const V&> U>
bst_Shynur::BST<K, V>::operator
std::multimap<J, U>() const& noexcept {

    std::multimap<J, U> mm{};

    for (const auto& [k, v] : *this)
        mm.insert(std::pair<J, U>{k, v});

    assert(mm.size() == size());

    return mm;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<std::constructible_from<const K&> J, std::constructible_from<V&&> U>
bst_Shynur::BST<K, V>::operator
std::multimap<J, U>() && noexcept {

    std::multimap<J, U> mm{};

    for (auto& [k, v] : *this)
        mm.insert(std::pair<J, U>{k, std::move(v)});

    assert(mm.size() == size());

    return ~BST(),
           mm;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<std::constructible_from<const K&> J, std::constructible_from<const V&> U>
bst_Shynur::BST<K, V>::operator
std::unordered_map<J, U>() const& noexcept {

    std::unordered_map<J, U> um{};

    for (const auto& [k, v] : *this)
        um.insert(std::pair<J, U>{k, v});

    assert(um.size() == size());

    return um;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<std::constructible_from<const K&> J, std::constructible_from<V&&> U>
bst_Shynur::BST<K, V>::operator
std::unordered_map<J, U>() && noexcept {

    std::unordered_map<J, U> um{};

    for (auto& [k, v] : *this)
        um.insert(std::pair<J, U>{k, std::move(v)});

    assert(um.size() == size());

    return ~BST(),
           um;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<std::constructible_from<const K&> J, std::constructible_from<const V&> U>
bst_Shynur::BST<K, V>::operator
std::unordered_multimap<J, U>() const& noexcept {

    std::unordered_multimap<J, U> umm{};

    for (const auto& [k, v] : *this)
        umm.insert(std::pair<J, U>{k, v});

    assert(umm.size() == size());

    return umm;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) template<std::constructible_from<const K&> J, std::constructible_from<V&&> U>
bst_Shynur::BST<K, V>::operator
std::unordered_multimap<J, U>() && noexcept {

    std::unordered_multimap<J, U> umm{};

    for (auto& [k, v] : *this)
        umm.insert(std::pair<J, U>{k, std::move(v)});

    assert(umm.size() == size());

    return ~BST(),
           umm;
}

// delete root's two subtrees and root's own element, and then delete the BST self;
// in fact, root's ~Node() will be called twice, so assigning nullptr to root's some member variables is necessary
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
bst_Shynur::BST<K, V>::~BST() noexcept {

    assert(size() >= 0 && root.p_parent == nullptr);

    static const constexpr struct {
        void operator()(const Node *const p_node) const noexcept {
            if (p_node->internal())
                (*this)(p_node->p_left), delete p_node->p_left,
                delete p_node->p,
                (*this)(p_node->p_right), delete p_node->p_right;
        }
    } wither_helper{};

    wither_helper(&root),
    root = {nullptr},
    size_ = 0;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::iterator::operator==(const iterator& b) const noexcept {

    return p_node == b.p_node;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::iterator::operator!=(const iterator& b) const noexcept {

    return p_node != b.p_node;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::Node::Entry&
bst_Shynur::BST<K, V>::iterator::operator*() const noexcept {

    return *p_node->p;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::Node::Entry *
bst_Shynur::BST<K, V>::iterator::operator->() const noexcept {

    return p_node->p;
}

// change pointer's destination to the next node if the next node is internal
// ohterwise, points to the most-right node, which is external
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline 
bst_Shynur::BST<K, V>::iterator&
bst_Shynur::BST<K, V>::iterator::operator++() noexcept {

    assert(p_node->internal());

    if (const Node *const p_next{p_node->p_next()}; p_next == nullptr) [[unlikely]]
        p_node = p_node->p_right;
    else
        p_node = p_next;

    return *this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::iterator&
bst_Shynur::BST<K, V>::iterator::operator--() noexcept {

    if (p_node->external())
        p_node = p_node->p_parent;
    else [[likely]]
        p_node = p_node->p_prev();

    return *this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::iterator
bst_Shynur::BST<K, V>::iterator::operator++(int) noexcept {

    assert(p_node->internal());

    iterator result{*this};

    return ++(*this), 
           result;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::iterator
bst_Shynur::BST<K, V>::iterator::operator--(int) noexcept {

    iterator result{*this};

    return --(*this),
           result;
}

// see Node::zag
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) 
bst_Shynur::BST<K, V>::Node&
bst_Shynur::BST<K, V>::Node::zig() noexcept {

    assert(internal() && internal_left());

    p_left->p_parent = p_parent;

    if (Node& zigged{*p_left}; is_root()) [[unlikely]]
        return std::swap(zigged, *(p_parent = this)),
               std::swap(p_left->p_parent, zigged.p_right->p_parent),
               zigged.p_left = p_right,
               p_right = &zigged,
               *this;
    else
        return zigged.p_right = (p_left = (p_parent = ptr_from_parent() = &zigged)->p_right)->p_parent = this,
               static_cast<Node&>(zigged);
}

// the reference returned is necessary
// because it indicates that the new node appeared at the position where this node has just invoke Node::zag
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) 
bst_Shynur::BST<K, V>::Node&
bst_Shynur::BST<K, V>::Node::zag() noexcept {

    assert(internal() && internal_right());

    p_right->p_parent = p_parent;

    if (Node& zagged{*p_right}; is_root()) [[unlikely]]
        return std::swap(zagged, *(p_parent = this)),
               std::swap(p_right->p_parent, zagged.p_left->p_parent),
               zagged.p_right = p_left,
               p_left = &zagged,
               *this;
    else
        return zagged.p_left = (p_right = (p_parent = ptr_from_parent() = &zagged)->p_left)->p_parent = this,
               static_cast<Node&>(zagged);
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::contains(const K& key) const noexcept {

    return search(key).internal();
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
const unsigned&
bst_Shynur::BST<K, V>::get_size_ref_for_Splay_() && noexcept {

    return size_;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
const bst_Shynur::BST<K, V>::Node&
bst_Shynur::BST<K, V>::get_root_ref_for_Splay_() && noexcept {

    return root;
}

// return internal node when this node does have a prev-node
// else, return begin node's left child, which is external
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
bst_Shynur::BST<K, V>::Node *
bst_Shynur::BST<K, V>::Node::p_prev() const noexcept {

    if (Node *p_cur_node; internal_left())
        for (p_cur_node = p_left; ; p_cur_node = p_cur_node->p_right)
            if (p_cur_node->internal_right()) [[likely]]
                continue;
            else
                return p_cur_node;
    else
        for (p_cur_node = const_cast<Node *>(this); ; p_cur_node = p_cur_node->p_parent)
            if (p_cur_node->is_root() || p_cur_node->is_right())
                return p_cur_node->p_parent;
            else [[likely]]
                continue;
}

// for best performance, the method is written hard to read
// please read Node::p_prev
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>)
bst_Shynur::BST<K, V>::Node *
bst_Shynur::BST<K, V>::Node::p_next() const noexcept {

    assert(internal());

    if (Node *p_cur_node, *p_next_node; internal_right())
        for (p_cur_node = p_right; ; p_cur_node = p_next_node)
            if (p_next_node = p_cur_node->p_left; p_next_node->internal()) [[likely]]
                continue;
            else
                return p_cur_node;
    else
        for (p_cur_node = const_cast<Node *>(this); ; p_cur_node = p_next_node)
            if ((p_next_node = p_cur_node->p_parent) == nullptr || p_cur_node == p_next_node->p_left)
                return p_next_node;
            else [[likely]]
                continue;    
}

// after inserting, the node is definitely a leaf
// its color will be changed to RED but height is still 0
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::Node&
bst_Shynur::BST<K, V>::Node::insert(const K& key, V val) noexcept {

    assert(external());

    return p = new Node::Entry{key, std::move(val)}, 
           p_left = new Node{this}, 
           p_right = new Node{this},
           color = RED,
           *this;
}

// delete this node and its element
// the method will change the way how nodes are linked to others
// return the reference of this node's replacer
// !!! the reference returned is necessary
// !!! because when this node is a root, it returns root, i.e. itself 
// !!! when a leaf, delete its two extenal nodes and return itself 
// !!! else, return its left or right internal child node
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::Node&
bst_Shynur::BST<K, V>::Node::del() noexcept {

    assert(internal() && (!internal_left() || !internal_right()));

    if (delete p; is_leaf())
        return delete p_left, 
               delete p_right,
               *this = {p_parent};
    else
        if (Node *const p_subtree{internal_left() ? (delete p_right, p_left) : (delete p_left, p_right)}; is_root()) [[unlikely]]
            return (*this = *p_subtree).p_parent = nullptr,
                   delete p_subtree,
                   *(p_left->p_parent = p_right->p_parent = this);
        else
            return (ptr_from_parent() = p_subtree)->p_parent = p_parent, 
                   delete this, 
                   *p_subtree;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::Node::internal() const noexcept {

    return p;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::Node::external() const noexcept {

    return !p;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::Node::is_root() const noexcept {

    return !p_parent;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::Node::internal_left() const noexcept {

    assert(internal());

    return p_left->internal();
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::Node::internal_right() const noexcept {

    assert(internal());

    return p_right->internal();
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::Node::is_leaf() const noexcept {

    assert(internal());

    return p_left->external() && p_right->external();
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::Node::is_left() const noexcept {

    assert(!is_root());

    return p_parent->p_left == this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bool
bst_Shynur::BST<K, V>::Node::is_right() const noexcept {

    assert(!is_root());

    return p_parent->p_right == this;
}

template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
bst_Shynur::BST<K, V>::Node *&
bst_Shynur::BST<K, V>::Node::ptr_from_parent() const noexcept {

    assert(!is_root());

    return is_left() ? p_parent->p_left : p_parent->p_right;
}

// return signed value so that can be compared with both signed or unsigned value
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
int
bst_Shynur::BST<K, V>::Node::get_height() const noexcept {

    return static_cast<int>(height);
}

// if K and V are both hashable, return hash(K) ^ hash(V)
// if K or V is not hashable, return 0
// else, return hash(K) or hash(V)
template<std::copy_constructible K, std::move_constructible V>requires(std::totally_ordered<K>) inline
std::size_t
bst_Shynur::BST<K, V>::Node::Entry::hash() const noexcept {

    if constexpr(requires() {std::hash<K>{}(key);})
        if constexpr(requires() {std::hash<V>{}(val);})
            return std::hash<K>{}(key) ^ std::hash<V>{}(val);
        else
            return std::hash<K>{}(key);
    else
        if constexpr(requires() {std::hash<V>{}(val);})
            return std::hash<V>{}(val);
        else
            return 0;
}
#endif
