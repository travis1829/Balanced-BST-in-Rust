use std::time::{Duration, Instant};
use rand::seq::SliceRandom;
use balanced_bst_in_rust::{BBST, LockedBBST, FastBBST, FastBBST2, FastBBST3};

const N: usize = 1_000_000;

fn test_BBST(arr: &Vec<usize>) {
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

    println!("test_BBST\t{:?}\t{:?}\t{:?}", d1, d2, d3);
}

fn test_LockedBBST(arr: &Vec<usize>) {
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

    println!("test_LockedBBST\t{:?}\t{:?}\t{:?}", d1, d2, d3);
}

fn test_FastBBST(arr: &Vec<usize>) {
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

    println!("test_FastBBST\t{:?}\t{:?}\t{:?}", d1, d2, d3);
}

fn test_FastBBST2(arr: &Vec<usize>) {
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

    println!("test_FastBBST2\t{:?}\t{:?}\t{:?}", d1, d2, d3);
}

fn test_FastBBST3(arr: &Vec<usize>) {
    let map = FastBBST3::new();
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

    println!("test_FastBBST3\t{:?}\t{:?}\t{:?}", d1, d2, d3);
}

fn test_all() {
    let mut arr = vec![0; N];
    let mut rng = rand::thread_rng();
    for i in 0..N {
        arr[i] = i;
    }

    println!(" --- test linear(0 ~ {})", N);
    test_BBST(&arr);
    test_LockedBBST(&arr);
    test_FastBBST(&arr);
    test_FastBBST2(&arr);
    test_FastBBST3(&arr);

    arr.shuffle(&mut rng);
    println!(" --- test random(uniformly distributed)");
    test_BBST(&arr);
    test_LockedBBST(&arr);
    test_FastBBST(&arr);
    test_FastBBST2(&arr);
    test_FastBBST3(&arr);
}

fn main() {
    test_all();
}
