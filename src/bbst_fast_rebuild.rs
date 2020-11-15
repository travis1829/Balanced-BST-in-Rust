/* A balanced binary search tree that uses a coarse grained lock
and parallelizes rebuilds for higher performance.
Searches are O(logN), and inserts/deletes are amortized O(logN) 
because rebuilds cost O(N). */

use std::ptr;
use std::sync::{Mutex};
use std::slice;
use crossbeam::thread;

const ALPHA_NOM: usize = 2;
const ALPHA_DENOM: usize = 3;
const THREAD_SPAWNING_SIZE: usize = 100_000;

/* Nodes in the tree that stores the key, value pair. */
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

/* A struct that stores pointers to nodes
and can be sent to other threads. */
struct Cursor<K, V> {
    ptr: *mut Node<K, V>,
}
unsafe impl<K, V> Send for Cursor<K, V> {}
unsafe impl<K, V> Sync for Cursor<K, V> {}

/* A tree data structure that stores key, value pairs. */
#[derive(Debug)]
pub struct FastBBST<K, V> {
    root: Mutex<*mut Node<K, V>>,
}
unsafe impl<K, V> Send for FastBBST<K, V> {}
unsafe impl<K, V> Sync for FastBBST<K, V> {}

impl<K: Eq + Ord + Clone, V: Clone> Node<K, V> {
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

impl<K, V> Cursor<K, V> {
    fn new(ptr: *mut Node<K, V>) -> Self {
        Cursor {
            ptr,
        }
    }
}
/*
impl<K, V> Clone for Cursor<K, V> {
    fn clone(&self) -> Self {
        Cursor(self.0.clone())
    }
}
*/

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

    /* Searches for a key.
    Returns Some(value) if exists. Otherwise, returns None. */
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

    /* Inserts a node to the tree.
    Rebuilds the tree if we need to.
    Returns true if successful, otherwise false. */
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

    /* Tries to insert a node under the node "node".
    Returns a tuple, whose first item is the result of the insertion (success / unsuccess),
    and the second item points to the root node of the subtree that needs to be rebuilt. */
    unsafe fn _insert<'a>(&'a self, node: &'a mut *mut Node<K, V>, key: K, value: V) -> (bool, Option<&'a mut *mut Node<K, V>>) {
        if *node == ptr::null_mut() {
            //does not exist... insert it here
            *node = Node::new(key, value);
            (true, None)
        }
        else if key == (**node).key {
            //already exists
            (false, None)
        }
        else {
            let result = if key < (**node).key 
                            { self._insert(&mut (**node).left, key, value) }
                        else
                            { self._insert(&mut (**node).right, key, value)};
            match result.0 {
                false => result,
                true => {
                    (**node).size += 1;
                    match (**node).is_unbalanced() {
                        false => result,
                        true => (true, Some(node)),
                    }
                }
            }
        }
    }

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

    unsafe fn _delete<'a>(&'a self, node: &'a mut *mut Node<K, V>, key: K) -> (bool, Option<&'a mut *mut Node<K, V>>) {
        if *node == ptr::null_mut() {
            //does not exist
            (false, None)
        }
        else if (**node).key == key {
            //found node
            if (**node).left == ptr::null_mut() {
                //node has only right child or no child nodes
                *node = (**node).right;
                (true, None)
            }
            else if (**node).right == ptr::null_mut() {
                //node has only left child or no child nodes
                *node = (**node).left;
                (true, None)
            }
            else {
                //node has two child nodes
                let successor = self._get_most_right((**node).left);            //get inorder predecessor
                std::mem::swap(&mut (**node).key, &mut (*successor).key);       //swap key with it
                std::mem::swap(&mut (**node).value, &mut (*successor).value);   //swap value with it
                let result = self._delete(&mut (**node).left, key);             //delete the swapped one. we know this will success
                (**node).size -= 1;
                match (**node).is_unbalanced() {
                    false => result,
                    true => (true, Some(node)),
                }
            }
        }
        else {
            let result = if key < (**node).key 
                            { self._delete(&mut (**node).left, key) }
                        else
                            { self._delete(&mut (**node).right, key)};
            match result.0 {
                false => result,
                true => {
                    (**node).size -= 1;
                    match (**node).is_unbalanced() {
                        false => result,
                        true => (true, Some(node)),
                    }
                }
            }
        }
    }

    //assumes node is non-null
    unsafe fn _get_most_right(&self, node: *mut Node<K, V>) -> *mut Node<K, V> {
        if (*node).right != ptr::null_mut()
            { self._get_most_right((*node).right) }
        else
            { node }
    }

    //assumes node is non-null
    unsafe fn _rebuild(&self, node: &mut *mut Node<K, V>) {
        //Create an empty array
        let mut vector : Vec<Cursor<K, V>> = Vec::with_capacity((**node).size);
        vector.set_len((**node).size);
        let mut array = vector.into_boxed_slice();

        //Rebuild the tree using the array
        self._into_array(Cursor::new(*node), &mut array[..]);
        *node = self._into_tree(&array[..]);
    }

    //assumes node is non-null
    unsafe fn _into_array(&self, cursor: Cursor<K, V>, array: &mut [Cursor<K, V>]) {
        /* Use crossbeam's scoped thread, because before this function ends, 
        we will always join with the thread created in this function. */
        thread::scope(|s| {
            let mut index = 0;

            //1. Process the left subtree, using a new thread if the subtree is big
            let wrapped_handler = 
            if (*cursor.ptr).left != ptr::null_mut() {
                let lcursor = Cursor::new((*cursor.ptr).left);
                index = (*lcursor.ptr).size;
                if index < THREAD_SPAWNING_SIZE {
                    self._into_array(lcursor, &mut array[..index]);
                    None
                }
                else {
                    let larray = slice::from_raw_parts_mut(array.as_mut_ptr(), index);
                    Some(s.spawn(move |_| {
                        self._into_array(lcursor, larray);
                    }))
                }
            }
            else {
                None
            };

            //2. Process the right subtree in this thread
            if (*cursor.ptr).right != ptr::null_mut() {
                let rcursor = Cursor::new((*cursor.ptr).right);
                self._into_array(rcursor, &mut array[index+1..]);
            }

            //3. Finish by writing at the array and joining with the thread (if exists)
            array[index] = cursor;
            if let Some(handler) = wrapped_handler {
                handler.join().unwrap();
            }
        }).unwrap();
    }

    fn _into_tree(&self, array: &[Cursor<K, V>]) -> *mut Node<K, V> {
        let size = array.len();
        if size == 0 {  //Empty
            ptr::null_mut()
        }
        else if size/2 < THREAD_SPAWNING_SIZE { //Small enough to be processed by a single thread
            unsafe {
                let node = array[size/2].ptr;
                (*node).left = self._into_tree(&array[..size/2]);
                (*node).right = self._into_tree(&array[size/2+1..]);
                (*node).size = size;
                node
            }
        }
        else {  //Process using multiple threads
            unsafe {
                thread::scope(|s| {
                    //1. Process the left part in a new thread
                    let larray = slice::from_raw_parts(array.as_ptr(), size/2);
                    let lhandler = s.spawn(move |_| {
                        Cursor::new(self._into_tree(larray))
                    });

                    //2. Process the right part in this thread
                    let node = array[size/2].ptr;
                    (*node).size = size;
                    (*node).right = self._into_tree(&array[size/2+1..]);

                    //3. Join with the thread
                    (*node).left = lhandler.join().unwrap().ptr;
                    node
                }).unwrap()
            }
        }
    }
}

impl<K, V> FastBBST<K, V> {
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