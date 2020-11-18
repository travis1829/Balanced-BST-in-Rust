use std::time::{Duration, Instant};
use rand::seq::SliceRandom;
use balanced_bst_in_rust::{BBST, LockedBBST, FastBBST, FastBBST2};

const N: usize = 1_000_000;

fn test_uniform_BBST() {
    let mut arr = vec![0; N];
    let mut rng = rand::thread_rng();
    for i in 0..N {
        arr[i] = i;
    }
    arr.shuffle(&mut rng);

    let map = BBST::new();
    let mut instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.insert(arr[i], i), true);
    }
    let d1 = instant.elapsed();

    instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.search(arr[i]), Some(i));
    }
    let d2 = instant.elapsed();

    instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.delete(arr[i]), true);
    }
    let d3 = instant.elapsed();

    println!("test_uniform_BBST\t{:?}\t{:?}\t{:?}", d1, d2, d3);
}

fn test_uniform_LockedBBST() {
    let mut arr = vec![0; N];
    let mut rng = rand::thread_rng();
    for i in 0..N {
        arr[i] = i;
    }
    arr.shuffle(&mut rng);

    let map = LockedBBST::new();
    let mut instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.insert(arr[i], i), true);
    }
    let d1 = instant.elapsed();

    instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.search(arr[i]), Some(i));
    }
    let d2 = instant.elapsed();

    instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.delete(arr[i]), true);
    }
    let d3 = instant.elapsed();

    println!("test_uniform_LockedBBST\t{:?}\t{:?}\t{:?}", d1, d2, d3);
}

fn test_uniform_FastBBST() {
    let mut arr = vec![0; N];
    let mut rng = rand::thread_rng();
    for i in 0..N {
        arr[i] = i;
    }
    arr.shuffle(&mut rng);

    let map = FastBBST::new();
    let mut instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.insert(arr[i], i), true);
    }
    let d1 = instant.elapsed();

    instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.search(arr[i]), Some(i));
    }
    let d2 = instant.elapsed();

    instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.delete(arr[i]), true);
    }
    let d3 = instant.elapsed();

    println!("test_uniform_FastBBST\t{:?}\t{:?}\t{:?}", d1, d2, d3);
}

fn test_uniform_FastBBST2() {
    let mut arr = vec![0; N];
    let mut rng = rand::thread_rng();
    for i in 0..N {
        arr[i] = i;
    }
    arr.shuffle(&mut rng);

    let map = FastBBST2::new();
    let mut instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.insert(arr[i], i), true);
    }
    let d1 = instant.elapsed();

    instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.search(arr[i]), Some(i));
    }
    let d2 = instant.elapsed();

    instant = Instant::now();
    for i in 0..N {
        assert_eq!(map.delete(arr[i]), true);
    }
    let d3 = instant.elapsed();

    println!("test_uniform_FastBBST\t{:?}\t{:?}\t{:?}", d1, d2, d3);
}

fn main() {
    test_uniform_BBST();
    test_uniform_LockedBBST();
    test_uniform_FastBBST();
    test_uniform_FastBBST2();
}
