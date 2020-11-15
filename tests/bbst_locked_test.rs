use balanced_bst_in_rust::LockedBBST;
use rand::seq::SliceRandom;

#[test]
fn test_basic() {
    let map = LockedBBST::new();
    //add key, values in random order
    assert_eq!(map.insert(3, 30), true);
    assert_eq!(map.insert(4, 40), true);
    assert_eq!(map.insert(1, 10), true);
    assert_eq!(map.insert(2, 20), true);
    assert_eq!(map.insert(5, 50), true);
    assert_eq!(map.insert(5, 10), false);

    //check size
    assert_eq!(map.is_empty(), false);
    assert_eq!(map.size(), 5);

    //check they exist
    for i in 1..6 {
        assert_eq!(map.search(i), Some(i * 10));
    }
    assert_eq!(map.search(6), None);

    //delete odd keys
    for i in 1..6 {
        if i % 2 != 0 {
            assert_eq!(map.delete(i), true);
        }
    }

    //check only even keys exist
    for i in 1..6 {
        if i % 2 != 0 {
            assert_eq!(map.search(i), None);
        }
        else {
            assert_eq!(map.search(i), Some(i * 10));
        }
    }
}

#[test]
fn test_rebuild() {
    let map = LockedBBST::new();
    for i in 1..101 {
        assert_eq!(map.insert(i, i * 10), true);
    }
    for i in 1..101 {
        assert_eq!(map.search(i), Some(i * 10));
    }
    for i in 1..51 {
        assert_eq!(map.delete(i), true);
    }
    for i in 1..101 {
        if i < 51 {
            assert_eq!(map.search(i), None);
        }
        else {
            assert_eq!(map.search(i), Some(i * 10));
        }
    }
}

#[test]
fn test_uniform() {
    const N: usize = 100_000;
    let mut arr = vec![0; N];
    let mut rng = rand::thread_rng();
    for i in 0..N {
        arr[i] = i;
    }
    arr.shuffle(&mut rng);

    let map = LockedBBST::new();
    for i in 0..N {
        assert_eq!(map.insert(arr[i], i), true);
    }

    for i in 0..N {
        assert_eq!(map.search(arr[i]), Some(i));
    }

    for i in 0..N {
        assert_eq!(map.delete(arr[i]), true);
    }
}