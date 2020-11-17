/* A balanced binary search tree that uses a coarse grained lock
and parallelizes rebuilds for higher performance.
Searches are O(logN), and inserts/deletes are amortized O(logN) 
because rebuilds cost O(N). */

use std::ptr;
use std::sync::{Mutex};
use std::slice;
use crossbeam::thread;
use crossbeam::channel::{unbounded, Sender, Receiver};

const ALPHA_NOM: usize = 2;
const ALPHA_DENOM: usize = 3;

const NUM_THREADS: usize = 16;
const THREAD_SPAWNING_SIZE: usize = 20_000;
const THREAD_SPAWNING_DEPTH: usize = 10;

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

struct WrappedArray<K, V> (*mut *mut Node<K, V>, usize);
unsafe impl<K, V> Send for WrappedArray<K, V> {}
unsafe impl<K, V> Sync for WrappedArray<K, V> {}

/* A tree data structure that stores key, value pairs. */
#[derive(Debug)]
pub struct FastBBST2<K, V> {
    root: Mutex<*mut Node<K, V>>,
}
unsafe impl<K, V> Send for FastBBST2<K, V> {}
unsafe impl<K, V> Sync for FastBBST2<K, V> {}

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

impl<K: Eq + Ord + Clone, V: Clone> FastBBST2<K, V> {
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
        let mut vector : Vec<*mut Node<K, V>> = Vec::with_capacity((**node).size);
        vector.set_len((**node).size);
        let mut array = vector.into_boxed_slice();

        //Rebuild the tree using the array
        if (**node).size < THREAD_SPAWNING_SIZE {
            self._into_array(*node, &mut array[..]);
            *node = self._into_tree(&array[..]);
        }
        else {
            //self._into_array(*node, &mut array[..]);
            let (node, mut array) = thread::scope(move |s| {
                let (sender, receiver) : (Sender<(Box<Node<K, V>>, WrappedArray<K, V>)>, Receiver<(Box<Node<K, V>>, WrappedArray<K, V>)>) = unbounded();
                let mut workers = Vec::with_capacity(NUM_THREADS);
                sender.send((Box::from_raw(*node), WrappedArray(array.as_mut_ptr(), array.len()))).unwrap();
                for _ in 0..NUM_THREADS {
                    let sender_clone = sender.clone();
                    let receiver_clone = receiver.clone();
                    workers.push(
                        s.spawn(move |_| loop {
                            let param_pair = receiver_clone.try_recv();
                            match param_pair {
                                Ok(param_pair) => {
                                    let (boxed_node, wrapped_array) = param_pair;
                                    self._into_array2(Box::into_raw(boxed_node),
                                                        slice::from_raw_parts_mut(wrapped_array.0, wrapped_array.1),
                                                        0,
                                                        &sender_clone);
                                },
                                Err(_) => return,
                            };
                        })
                    );
                }
                loop {
                    let param_pair = receiver.try_recv();
                    match param_pair {
                        Ok(param_pair) => {
                            let (boxed_node, wrapped_array) = param_pair;
                            self._into_array2(Box::into_raw(boxed_node),
                                                slice::from_raw_parts_mut(wrapped_array.0, wrapped_array.1),
                                                0,
                                                &sender);
                        },
                        Err(_) => break,
                    }
                }
                (node, array)
            }).unwrap();


            //*node = self._into_tree(&array[..]);
            thread::scope(move |s| {
                let (sender, receiver) : (Sender<WrappedArray<K, V>>, Receiver<WrappedArray<K, V>>) = unbounded();
                let mut workers = Vec::with_capacity(NUM_THREADS);
                sender.send(WrappedArray(array.as_mut_ptr(), array.len())).unwrap();
                for _ in 0..NUM_THREADS {
                    let sender_clone = sender.clone();
                    let receiver_clone = receiver.clone();
                    workers.push(
                        s.spawn(move |_| loop {
                            let param = receiver_clone.try_recv();
                            match param {
                                Ok(wrapped_array) => {
                                    self._into_tree2(slice::from_raw_parts_mut(wrapped_array.0, wrapped_array.1),
                                                    0,
                                                    &sender_clone);
                                },
                                Err(_) => return,
                            };
                        })
                    );
                }
                loop {
                    let param = receiver.try_recv();
                    match param {
                        Ok(wrapped_array) => {
                            self._into_tree2(slice::from_raw_parts_mut(wrapped_array.0, wrapped_array.1),
                                            0,
                                            &sender);
                        },
                        Err(_) => break,
                    }
                }
                *node = array[array.len()/2];
            }).unwrap();
        }
    }

    //assumes node is non-null
    unsafe fn _into_array(&self, node: *mut Node<K, V>, array: &mut [*mut Node<K, V>]) {
        let mut index = 0;
        if (*node).left != ptr::null_mut() {
            index = (*(*node).left).size;
            self._into_array((*node).left, &mut array[..index]);
        }
        array[index] = node;
        if (*node).right != ptr::null_mut() {
            self._into_array((*node).right, &mut array[index+1..]);
        }
    }

    fn _into_tree(&self, array: &[*mut Node<K, V>]) -> *mut Node<K, V> {
        let size = array.len();
        if size == 0 {
            ptr::null_mut()
        }
        else {
            unsafe {
                let node = array[size/2];
                (*node).left = self._into_tree(&array[..size/2]);
                (*node).right = self._into_tree(&array[size/2+1..]);
                (*node).size = size;
                node
            }
        }
    }

    //assumes node is non-null
    unsafe fn _into_array2(&self, node: *mut Node<K, V>, array: &mut [*mut Node<K, V>], depth: usize, sender: &Sender<(Box<Node<K, V>>, WrappedArray<K, V>)>) {
        let mut index = 0;
        if (*node).left != ptr::null_mut() {
            index = (*(*node).left).size;
            if depth == THREAD_SPAWNING_DEPTH && index >= THREAD_SPAWNING_SIZE {
                sender.send((Box::from_raw((*node).left), WrappedArray(array.as_mut_ptr(), index))).unwrap();
            }
            else {
                self._into_array2((*node).left, &mut array[..index], depth+1, sender);
            }
        }
        array[index] = node;
        if (*node).right != ptr::null_mut() {
            if depth == THREAD_SPAWNING_DEPTH && (*(*node).right).size >= THREAD_SPAWNING_SIZE {
                sender.send((Box::from_raw((*node).left), WrappedArray(array.as_mut_ptr().add(index+1), array.len() - index - 1))).unwrap();
            }
            else {
                self._into_array2((*node).right, &mut array[index+1..], depth+1, sender);
            }
        }
    }

    //assumes length is nonzero
    unsafe fn _into_tree2(&self, array: &mut [*mut Node<K, V>], depth: usize, sender: &Sender<WrappedArray<K, V>>) {
        let size = array.len();
        if depth == THREAD_SPAWNING_DEPTH && size/2 >= THREAD_SPAWNING_SIZE {
            sender.send(WrappedArray(array.as_mut_ptr(), size/2)).unwrap();
        }
        else if size/2 != 0 {
            self._into_tree2(&mut array[..size/2], depth+1, sender);
        }
        if depth == THREAD_SPAWNING_DEPTH && (size - size/2 - 1) >= THREAD_SPAWNING_SIZE {
            sender.send(WrappedArray(array.as_mut_ptr().add(size/2+1), size-size/2-1)).unwrap();
        }
        else if size-size/2-1 != 0 {
            self._into_tree2(&mut array[size/2+1..], depth+1, sender);
        }
        let node = array[size/2];
        (*node).left = if size/2 != 0 { array[size/2/2] } else { ptr::null_mut() };
        (*node).right = if size-size/2-1 != 0 { array[(size/2+1+size)/2] } else { ptr::null_mut() };
    }
}

impl<K, V> FastBBST2<K, V> {
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

impl<K, V> Drop for FastBBST2<K, V> {
    fn drop(&mut self) {
        self.clear();
    }
}