/// A weight balanced binary search tree that uses a coarse grained lock
/// and parallelizes rebuilds for higher performance.
/// Searches are O(logN), and inserts/deletes are amortized O(logN) 
/// because rebuilds cost O(N).

use std::ptr;
use std::sync::{Mutex};
use std::slice;
use crossbeam::thread;

/// A fraction that represents the ALPHA of the weight balanced tree.
const ALPHA_NOM: usize = 4;
const ALPHA_DENOM: usize = 7;

const THREAD_SPAWNING_SIZE: usize = 10_000; //we spawn a new thread if the subtree's size is bigger than this
const THREAD_SPAWNING_DEPTH: usize = 4; //results in max 2^(n+1) threads

/// A node in the tree that stores a key, value pair, the size of the subtree rooted by it,
/// and a pointer to its left, right child node.
#[derive(Debug)]
struct Node<K, V> {
    key: K,
    value: V,
    size: usize,
    left: *mut Node<K, V>,
    right: *mut Node<K, V>,
}
unsafe impl<K, V> Send for Node<K, V> {}
unsafe impl<K, V> Sync for Node<K, V> {}

/// A struct that wraps a mutable pointer to a slice of `*mut Node<K, V>`s.
/// Can be safely sent to other threads.
struct WrappedArray<K, V> (*mut *mut Node<K, V>);
unsafe impl<K, V> Send for WrappedArray<K, V> {}
unsafe impl<K, V> Sync for WrappedArray<K, V> {}

/// A coarse grain locked tree data structure that stores key, value pairs.
/// Rebuild operations are parallelized.
#[derive(Debug)]
pub struct FastBBST<K, V> {
    root: Mutex<*mut Node<K, V>>,
}
unsafe impl<K, V> Send for FastBBST<K, V> {}
unsafe impl<K, V> Sync for FastBBST<K, V> {}

impl<K: Eq + Ord + Clone, V: Clone> Node<K, V> {
    /// Makes a new node using `Box::new`, and returns a raw pointer to the node.
    fn new(key: K, value: V) -> *mut Self {
        Box::into_raw(Box::new(Self {
            key,
            value,
            size: 1,
            left: ptr::null_mut(),
            right: ptr::null_mut(),
        }))
    }
}

impl<K, V> Node<K, V> {
    /// Returns `true` if the subtree rooted by this node is unbalanced. Otherwise, returns `false`.
    fn is_unbalanced(&self) -> bool {
        unsafe {
            if self.left != ptr::null_mut() && (*self.left).size * ALPHA_DENOM > self.size * ALPHA_NOM {
                true
            }
            else if self.right != ptr::null_mut() && (*self.right).size * ALPHA_DENOM > self.size * ALPHA_NOM {
                true
            }
            else {
                false
            }
        }
    }
}

impl<K: Eq + Ord + Clone, V: Clone> FastBBST<K, V> {
    pub fn new() -> Self {
        Self {
            root: Mutex::new(ptr::null_mut()),
        }
    }

    pub fn is_empty(&self) -> bool {
        *self.root.lock().unwrap() == ptr::null_mut()
    }

    pub fn size(&self) -> usize {
        let root_guard = self.root.lock().unwrap();
        if *root_guard == ptr::null_mut() {
            0
        }
        else {
            unsafe {
                (**root_guard).size
            }
        }
    }

    /// Searches for a key, starting from the root node.
    /// Returns `Some(value)` if exists. Otherwise, returns `None`.
    pub fn search(&self, key: K) -> Option<V> {
        self._search(&*self.root.lock().unwrap(), key)
    }

    fn _search(&self, node: &*mut Node<K, V>, key: K) -> Option<V> {
        unsafe {
            if *node == ptr::null_mut() {
                None
            }
            else if key < (**node).key {
                self._search(&(**node).left, key)
            }
            else if key > (**node).key {
                self._search(&(**node).right, key)
            }
            else {
                Some((**node).value.clone())
            }
        }
    }

    /// Inserts the `key`, `value` pair in the tree.
    /// Rebuilds the tree if we need to.
    /// Returns `true` if successful, otherwise `false`.
    pub fn insert(&self, key: K, value: V) -> bool {
        let mut root_guard = self.root.lock().unwrap();
        unsafe {
            let result = self._insert(&mut *root_guard, key, value);
            if let Some(node) = result.1 {
                self._rebuild(node);
            }
            result.0
        }
    }

    /// Tries to insert a node under the node `node`.
    /// Returns a tuple, whose first item is the result of the insertion (`true` if successful, otherwise `false`),
    /// and the second item optionally points to the root node of the subtree that needs to be rebuilt.
    unsafe fn _insert<'a>(&'a self, node: &'a mut *mut Node<K, V>, key: K, value: V) -> (bool, Option<&'a mut *mut Node<K, V>>) {
        if *node == ptr::null_mut() {
            //key does not exist. insert it here
            *node = Node::new(key, value);
            (true, None)
        }
        else if key == (**node).key {
            //already exists
            (false, None)
        }
        else {
            //get result of the recursive call
            let result = if key < (**node).key 
                            { self._insert(&mut (**node).left, key, value) }
                        else
                            { self._insert(&mut (**node).right, key, value)};
            match result.0 {
                false => result,
                true => { //successful insertion. now, this node may be unbalanced
                    (**node).size += 1;
                    match (**node).is_unbalanced() {
                        false => result,
                        true => (true, Some(node)),
                    }
                }
            }
        }
    }

    /// Deletes `key` (and its associated value) in the tree.
    /// Rebuilds the tree if we need to.
    /// Returns `true` if successful, otherwise `false`. */
    pub fn delete(&self, key: K) -> bool {
        let mut root_guard = self.root.lock().unwrap();
        unsafe {
            let result = self._delete(&mut *root_guard, key);
            if let Some(node) = result.1 {
                self._rebuild(node);
            }
            result.0
        }
    }

    /// Tries to delete a node under the node `node`.
    // Returns a tuple, whose first item is the result of the insertion (`true` if successful, otherwise `false`),
    /// and the second item optionally points to the root node of the subtree that needs to be rebuilt. */
    unsafe fn _delete<'a>(&'a self, node: &'a mut *mut Node<K, V>, key: K) -> (bool, Option<&'a mut *mut Node<K, V>>) {
        if *node == ptr::null_mut() {
            //does not exist
            (false, None)
        }
        else if (**node).key == key {
            //found node
            if (**node).left == ptr::null_mut() {
                //node only has a right child or no child
                *node = (**node).right;
                (true, None)
            }
            else if (**node).right == ptr::null_mut() {
                //node only has a left child
                *node = (**node).left;
                (true, None)
            }
            else {
                //node has two child nodes
                let predecessor = self._get_most_right((**node).left);          //get inorder predecessor
                std::mem::swap(&mut (**node).key, &mut (*predecessor).key);     //swap key with it
                std::mem::swap(&mut (**node).value, &mut (*predecessor).value); //swap value with it
                let result = self._delete(&mut (**node).left, key);             //delete the swapped one. we know this will success
                (**node).size -= 1;
                //now, this node may be unbalanced
                match (**node).is_unbalanced() {
                    false => result,
                    true => (true, Some(node)),
                }
            }
        }
        else {
            //get result of the recursive call
            let result = if key < (**node).key 
                            { self._delete(&mut (**node).left, key) }
                        else
                            { self._delete(&mut (**node).right, key)};
            match result.0 {
                false => result,
                true => { //successful deletion. now, this node may be unbalanced
                    (**node).size -= 1;
                    match (**node).is_unbalanced() {
                        false => result,
                        true => (true, Some(node)),
                    }
                }
            }
        }
    }

    /// Finds the rightmost node of `node`.
    /// Unsafe since assumes that `node` is non-null. */
    unsafe fn _get_most_right(&self, node: *mut Node<K, V>) -> *mut Node<K, V> {
        if (*node).right != ptr::null_mut()
            { self._get_most_right((*node).right) }
        else
            { node }
    }

    /// Rebuilds the subtree rooted by `node`. The pointer that `node` references may change after a call to this function.
    /// Unsafe since assumes that `node` refers a non-null pointer.
    unsafe fn _rebuild(&self, node: &mut *mut Node<K, V>) {
        //Create an empty array
        let mut vector : Vec<*mut Node<K, V>> = Vec::with_capacity((**node).size);
        vector.set_len((**node).size);
        let mut array = vector.into_boxed_slice();

        //Rebuild the tree using the array
        self._into_array(*node, &mut array[..], 0);
        *node = self._into_tree(&mut array[..], 0);
    }

    /// For each node in the subtree rooted by `node`, in sorted order,
    /// we copy a pointer to it to `array`.
    unsafe fn _into_array(&self, node: *mut Node<K, V>, array: &mut [*mut Node<K, V>], depth: usize) {
        if (*node).left == ptr::null_mut() || depth > THREAD_SPAWNING_DEPTH || (*(*node).left).size < THREAD_SPAWNING_SIZE {
            //Handle it in this thread
            let mut index = 0;
            if (*node).left != ptr::null_mut() {
                index = (*(*node).left).size;
                self._into_array((*node).left, &mut array[..index], depth+1);
            }
            array[index] = node;
            if (*node).right != ptr::null_mut() {
                self._into_array((*node).right, &mut array[index+1..], depth+1);
            }
        }
        else {
            //Handle it in another thread
            /* Use crossbeam's scoped thread, because before this function ends, 
            we will always join with the thread created in this function. */
            thread::scope(|s| {
                let index = (*(*node).left).size;
                let node_in_box = Box::from_raw((*node).left);
                let wrapped_array = WrappedArray(array.as_mut_ptr());
                s.spawn(move |_| {
                    let node_ptr = Box::into_raw(node_in_box);
                    let larray = slice::from_raw_parts_mut(wrapped_array.0, index);
                    self._into_array(node_ptr, larray, depth+1);
                });
                array[index] = node;
                if (*node).right != ptr::null_mut() {
                    self._into_array((*node).right, &mut array[index+1..], depth+1);
                }
            }).unwrap();
        }
    }

    /// Creates a perfectly balanced subtree that contains all nodes in `array`, and returns a pointer to its root node.
    fn _into_tree(&self, array: &mut [*mut Node<K, V>], depth: usize) -> *mut Node<K, V> {
        let size = array.len();
        if size == 0 {
            ptr::null_mut()
        }
        else if depth > THREAD_SPAWNING_DEPTH || size < THREAD_SPAWNING_SIZE {
            //Handle it in this thread
            unsafe {
                let node = array[size/2];
                (*node).left = self._into_tree(&mut array[..size/2], depth+1);
                (*node).right = self._into_tree(&mut array[size/2+1..], depth+1);
                (*node).size = size;
                node
            }
        }
        else {
            //Handle it in another thread
            unsafe {
                thread::scope(|s| {
                    let node = array[size/2];
                    let wrapped_array = WrappedArray(array.as_mut_ptr());
                    let handler = s.spawn(move |_| {
                        let larray = slice::from_raw_parts_mut(wrapped_array.0, size/2);
                        let result = self._into_tree(larray, depth+1);
                        Box::from_raw(result)
                    });
                    (*node).right = self._into_tree(&mut array[size/2+1..], depth+1);
                    (*node).left = Box::into_raw(handler.join().unwrap());
                    (*node).size = size;
                    node
                }).unwrap()
            }
        }
    }
}

impl<K, V> FastBBST<K, V> {
    /// Empties the tree.
    fn clear(&self) {
        let mut root_guard = self.root.lock().unwrap();
        self._clear(*root_guard);
        *root_guard = ptr::null_mut();
    }

    fn _clear(&self, node: *mut Node<K, V>) {
        if node != ptr::null_mut() {
            unsafe {
                self._clear((*node).left);
                self._clear((*node).right);
                drop(Box::from_raw(node));
            }
        }
    }
}

impl<K, V> Drop for FastBBST<K, V> {
    fn drop(&mut self) {
        self.clear();
    }
}