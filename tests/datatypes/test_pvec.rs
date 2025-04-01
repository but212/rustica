use rustica::pvec;
use rustica::pvec::PersistentVector;

#[test]
fn test_new() {
    let vec: PersistentVector<i32> = PersistentVector::new();
    assert_eq!(vec.len(), 0);
    assert!(vec.is_empty());
}

#[test]
fn test_unit() {
    let vec = PersistentVector::unit(42);
    assert_eq!(vec.len(), 1);
    assert_eq!(vec.get(0), Some(&42));
    assert!(!vec.is_empty());
}

#[test]
fn test_from_slice() {
    let data = [1, 2, 3, 4];
    let vec = PersistentVector::from_slice(&data);
    
    assert_eq!(vec.len(), 4);
    assert_eq!(vec.get(0), Some(&1));
    assert_eq!(vec.get(1), Some(&2));
    assert_eq!(vec.get(2), Some(&3));
    assert_eq!(vec.get(3), Some(&4));
    assert_eq!(vec.get(4), None);
}

#[test]
fn test_push_back_and_get() {
    let vec = PersistentVector::<i32>::new()
        .push_back(1)
        .push_back(2)
        .push_back(3);

    assert_eq!(vec.len(), 3);
    assert_eq!(vec.get(0), Some(&1));
    assert_eq!(vec.get(1), Some(&2));
    assert_eq!(vec.get(2), Some(&3));
    assert_eq!(vec.get(3), None);
}

#[test]
fn test_pop_back() {
    let vec = pvec![1, 2, 3, 4];

    let result = vec.pop_back();
    assert!(result.is_some());
    let (vec2, value) = result.unwrap();
    assert_eq!(value, 4);
    assert_eq!(vec2.len(), 3);

    let result = vec2.pop_back();
    assert!(result.is_some());
    let (vec3, value) = result.unwrap();
    assert_eq!(value, 3);
    assert_eq!(vec3.len(), 2);

    let result = vec3.pop_back();
    assert!(result.is_some());
    let (vec4, value) = result.unwrap();
    assert_eq!(value, 2);
    assert_eq!(vec4.len(), 1);

    let result = vec4.pop_back();
    assert!(result.is_some());
    let (vec5, value) = result.unwrap();
    assert_eq!(value, 1);
    assert_eq!(vec5.len(), 0);

    assert!(vec5.pop_back().is_none());
}

#[test]
fn test_update() {
    let vec = pvec![1, 2, 3, 4];

    let vec2 = vec.update(1, 20);
    assert_eq!(vec2.get(1), Some(&20));

    // Original vector is unchanged
    assert_eq!(vec.get(1), Some(&2));

    // Out of bounds update is safe
    let vec3 = vec.update(10, 100);
    assert_eq!(vec3.len(), vec.len());
}

#[test]
fn test_map() {
    let vec = pvec![1, 2, 3, 4];

    let doubled = vec.map(|x| x * 2);
    assert_eq!(doubled.len(), 4);
    assert_eq!(doubled.get(0), Some(&2));
    assert_eq!(doubled.get(1), Some(&4));
    assert_eq!(doubled.get(2), Some(&6));
    assert_eq!(doubled.get(3), Some(&8));
}

#[test]
fn test_filter() {
    let vec = pvec![1, 2, 3, 4, 5];

    let even = vec.filter(|&x| x % 2 == 0);
    assert_eq!(even.len(), 2);
    
    // Convert to standard Vec for easier comparison
    let even_vec = even.to_vec();
    assert_eq!(even_vec, vec![2, 4]);
}

#[test]
fn test_concatenation() {
    let vec1 = pvec![1, 2, 3];
    let vec2 = pvec![4, 5, 6];

    let concatenated = vec1.concat(&vec2);
    
    assert_eq!(concatenated.len(), 6);
    
    // Convert to standard Vec for easier comparison
    let concat_vec = concatenated.to_vec();
    assert_eq!(concat_vec, vec![1, 2, 3, 4, 5, 6]);
}

#[test]
fn test_iteration() {
    let vec = pvec![1, 2, 3, 4];

    // Test sum
    let mut sum = 0;
    for &n in vec.iter() {
        sum += n;
    }
    assert_eq!(sum, 10);

    // Test product
    let mut product = 1;
    for &n in vec.iter() {
        product *= n;
    }
    assert_eq!(product, 24);

    // Test with iterator methods
    assert!(vec.iter().all(|&x| x > 0));
    assert!(vec.iter().any(|&x| x % 2 == 0));
}

#[test]
fn test_macro() {
    // Test empty vector
    let empty_vec: PersistentVector<i32> = pvec![];
    assert_eq!(empty_vec.len(), 0);
    
    // Test vector with elements
    let vec = pvec![1, 2, 3];
    assert_eq!(vec.len(), 3);
    assert_eq!(vec.get(0), Some(&1));
    
    // Test vector with trailing comma
    let trailing = pvec![4, 5, 6,];
    assert_eq!(trailing.len(), 3);
    assert_eq!(trailing.get(2), Some(&6));
}

#[test]
fn test_from_iter() {
    // Test FromIterator implementation
    let std_vec = vec![1, 2, 3];
    
    // Using collect
    let pvec: PersistentVector<_> = std_vec.iter().cloned().collect();
    assert_eq!(pvec.len(), 3);
    assert_eq!(pvec.get(0), Some(&1));
    
    // Using from_iter
    let pvec2 = PersistentVector::from_iter(vec![4, 5, 6]);
    assert_eq!(pvec2.to_vec(), vec![4, 5, 6]);
}

#[test]
fn test_iterator() {
    let vec = pvec![1, 2, 3];

    let mut iter = vec.iter();
    assert_eq!(iter.next(), Some(&1));
    assert_eq!(iter.next(), Some(&2));
    assert_eq!(iter.next(), Some(&3));
    assert_eq!(iter.next(), None);

    // Test iterator conversion
    let collected: Vec<i32> = vec.iter().cloned().collect();
    assert_eq!(collected, vec![1, 2, 3]);
}

#[test]
fn test_index() {
    let vec = pvec![10, 20, 30];

    // Access using index operator
    assert_eq!(vec[0], 10);
    assert_eq!(vec[1], 20);
    assert_eq!(vec[2], 30);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn test_index_panic() {
    let vec = pvec![1, 2, 3];
    let _ = vec[10]; // This should panic
}

#[test]
fn test_sorted() {
    let vec = pvec![3, 1, 4, 2];

    let sorted: Vec<&i32> = vec.sorted().collect();
    assert_eq!(sorted, vec![&1, &2, &3, &4]);
}

#[test]
fn test_large_vector() {
    // Create a vector with many elements to test tree structure
    let mut vec = PersistentVector::<i32>::new();

    // Add 100 elements and verify the vector as we go
    for i in 0..100 {
        vec = vec.push_back(i);
        
        // Print every 10th element to debug the issue
        if i % 10 == 0 {
            println!("Added element {}, length is {}", i, vec.len());
        }
    }

    // Check if we can access elements at various positions
    for i in 0..100 {
        if i % 10 == 0 {
            println!("Checking index {}: {:?}", i, vec.get(i));
        }
    }

    // Check some specific access points
    println!("Element at index 0: {:?}", vec.get(0));
    println!("Element at index 31: {:?}", vec.get(31));
    println!("Element at index 32: {:?}", vec.get(32));
    println!("Element at index 33: {:?}", vec.get(33));
    println!("Element at index 63: {:?}", vec.get(63));
    println!("Element at index 64: {:?}", vec.get(64));
    
    // Test updating elements at critical boundaries
    let updated_vec = vec.update(31, 310);
    let updated_vec2 = updated_vec.update(32, 320);
    
    println!("Updated element at index 31: {:?}", updated_vec.get(31));
    println!("Updated element at index 32: {:?}", updated_vec2.get(32));
    
    // Original should remain unchanged
    println!("Original element at index 31: {:?}", vec.get(31));
    println!("Original element at index 32: {:?}", vec.get(32));
    
    assert_eq!(vec.get(31), Some(&31), "Failed to get element at index 31");
    assert_eq!(vec.get(32), Some(&32), "Failed to get element at index 32");
    assert_eq!(updated_vec.get(31), Some(&310), "Failed to update element at index 31");
    assert_eq!(updated_vec2.get(32), Some(&320), "Failed to update element at index 32");
}

#[test]
fn test_persistence() {
    // Test that the data structure is truly persistent
    let v1 = pvec![1, 2, 3];
    let v2 = v1.push_back(4);
    let v3 = v1.push_back(5);

    // v1 is still [1,2,3]
    assert_eq!(v1.len(), 3);
    assert_eq!(v1.get(0), Some(&1));
    assert_eq!(v1.get(2), Some(&3));

    // v2 is [1,2,3,4]
    assert_eq!(v2.len(), 4);
    assert_eq!(v2.get(3), Some(&4));

    // v3 is [1,2,3,5]
    assert_eq!(v3.len(), 4);
    assert_eq!(v3.get(3), Some(&5));
}

#[test]
fn test_chunks() {
    let vec = pvec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    // Test getting chunks with default size
    let chunks: Vec<Vec<i32>> = vec.chunks().collect();
    
    // Verify we get chunks (exact size depends on implementation defaults)
    assert!(!chunks.is_empty());
    
    // Check that all elements are present when rejoined
    let rejoined: Vec<i32> = chunks.into_iter().flatten().collect();
    assert_eq!(rejoined, vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
}

#[test]
fn test_first_last() {
    let vec = pvec![1, 2, 3, 4, 5];
    
    assert_eq!(vec.first(), Some(&1));
    assert_eq!(vec.last(), Some(&5));
    
    let empty: PersistentVector<i32> = PersistentVector::new();
    assert_eq!(empty.first(), None);
    assert_eq!(empty.last(), None);
}

#[test]
fn test_into_iter() {
    let vec = pvec![1, 2, 3];
    
    // Test consuming iterator
    let sum: i32 = vec.into_iter().sum();
    assert_eq!(sum, 6);
}

#[test]
fn test_to_vec() {
    let vec = pvec![1, 2, 3, 4, 5];
    
    let std_vec = vec.to_vec();
    assert_eq!(std_vec, vec![1, 2, 3, 4, 5]);
}

#[test]
fn test_to_arc() {
    let vec = pvec![1, 2, 3];
    let arc_vec = vec.to_arc();
    
    assert_eq!(arc_vec.len(), 3);
    assert_eq!(arc_vec.get(0), Some(&1));
}

#[test]
fn test_tree_structure_debugging() {
    use rustica::pvec::tree::Tree;
    
    // 트리 구조 디버깅용 테스트
    println!("Creating empty tree");
    let mut tree = Tree::<i32>::new();
    
    // 첫 32개 요소를 추가하고 구조 확인
    for i in 0..32 {
        tree = tree.push_back(i);
        if i % 8 == 0 {
            println!("Added {} elements, tree size: {}", i+1, tree.len());
        }
    }
    
    // 첫 청크가 가득 찼을 때의 구조 확인
    println!("First chunk filled. Tree size: {}", tree.len());
    
    // 인덱스 접근 확인
    for i in 28..32 {
        println!("Element at index {}: {:?}", i, tree.get(i));
    }
    
    // 33번째 요소 추가 시 확인
    tree = tree.push_back(32);
    println!("Added 33rd element, tree size: {}", tree.len());
    
    // 인덱스 31과 32의 요소 확인
    println!("Element at index 31: {:?}", tree.get(31));
    println!("Element at index 32: {:?}", tree.get(32));
    
    // 추가 요소 확인
    for i in 33..40 {
        tree = tree.push_back(i);
    }
    
    println!("Added 40 elements, tree size: {}", tree.len());
    
    // 다양한 위치의 요소 확인
    println!("Element at index 0: {:?}", tree.get(0));
    println!("Element at index 31: {:?}", tree.get(31));
    println!("Element at index 32: {:?}", tree.get(32));
    println!("Element at index 39: {:?}", tree.get(39));
    
    // 범위별 요소 확인 (임계값 주변)
    println!("Elements around chunk boundaries:");
    for i in 30..40 {
        println!("Index {}: {:?}", i, tree.get(i));
    }
    
    // 검증
    assert_eq!(tree.get(31), Some(&31), "Element at index 31 should be 31");
    assert_eq!(tree.get(32), Some(&32), "Element at index 32 should be 32");
    assert_eq!(tree.get(39), Some(&39), "Element at index 39 should be 39");
}