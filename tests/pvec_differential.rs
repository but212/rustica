use quickcheck::TestResult;
use quickcheck_macros::quickcheck;
use rustica::pvec::PersistentVector;

#[test]
fn test_pvec_height_2_update() {
    // 3000 elements forces height 2 tree (since height 1 max is 2048 + tail/head)
    let n = 3000;
    let mut pvec: PersistentVector<i32> = (0..n).collect();
    let mut std_vec: Vec<i32> = (0..n).collect();

    // Update at index 2000 and 2500 (deep in the tree)
    pvec = pvec.update(2000, 99999);
    std_vec[2000] = 99999;

    pvec = pvec.update(2500, 88888);
    std_vec[2500] = 88888;

    assert_eq!(pvec.get(2000), Some(&99999));
    assert_eq!(pvec.get(2500), Some(&88888));
    assert_eq!(pvec.get(1999), Some(&1999));
    assert_eq!(pvec.to_vec(), std_vec);
}

#[test]
fn test_pvec_height_2_split_concat() {
    let n = 3500;
    let pvec: PersistentVector<usize> = (0..n).collect();
    let std_vec: Vec<usize> = (0..n).collect();

    let split_point = 2500;
    let (left, right) = pvec.split_at(split_point);

    assert_eq!(left.to_vec(), std_vec[..split_point].to_vec());
    assert_eq!(right.to_vec(), std_vec[split_point..].to_vec());

    let recombined = left.concat(&right);
    assert_eq!(recombined.to_vec(), std_vec);
}

#[test]
fn test_pvec_height_2_push_front_split_regression() {
    let mut pvec: PersistentVector<i32> = (0..5000).collect();
    let original: Vec<i32> = (0..5000).collect();

    for i in 0..65 {
        pvec = pvec.push_front(-(i + 1));
    }

    assert_eq!(pvec.len(), 5065);

    let (left, right) = pvec.split_at(65);
    assert_eq!(left.len(), 65);
    assert_eq!(right.len(), 5000);

    let expected_left: Vec<i32> = (1..=65).rev().map(|x| -x).collect();
    assert_eq!(left.to_vec(), expected_left);
    assert_eq!(right.to_vec(), original);

    let recombined = left.concat(&right);
    assert_eq!(recombined.len(), 5065);
    assert_eq!(recombined.to_vec(), pvec.to_vec());
}

#[test]
fn test_pvec_height_2_push_back_split_regression() {
    let mut pvec: PersistentVector<i32> = (0..5000).collect();
    let original: Vec<i32> = (0..5000).collect();

    for i in 0..65 {
        pvec = pvec.push_back(5000 + i);
    }

    assert_eq!(pvec.len(), 5065);

    let (left, right) = pvec.split_at(5000);
    assert_eq!(left.len(), 5000);
    assert_eq!(right.len(), 65);

    let expected_right: Vec<i32> = (5000..5065).collect();
    assert_eq!(left.to_vec(), original);
    assert_eq!(right.to_vec(), expected_right);

    let recombined = left.concat(&right);
    assert_eq!(recombined.len(), 5065);
    assert_eq!(recombined.to_vec(), pvec.to_vec());
}

#[test]
fn test_qc_reproduction() {
    let args: (usize, Vec<(u8, usize, i32)>) = (
        53698841838081727,
        vec![
            (156, 0, 0),
            (65, 0, 0),
            (104, 0, 0),
            (23, 0, 0),
            (1, 0, 0),
            (8, 0, 0),
            (156, 0, 0),
            (8, 0, 0),
            (93, 0, 0),
            (128, 0, 0),
            (51, 0, 0),
            (55, 0, 0),
            (54, 6639855796709034675, 0),
            (222, 1485137373559459709, 0),
        ],
    );
    let init_len = args.0 % 3500;
    let mut pvec: PersistentVector<i32> = (0..init_len as i32).collect();
    let mut std_vec: Vec<i32> = (0..init_len as i32).collect();

    for (step, (op, raw_idx, val)) in args.1.into_iter().enumerate() {
        match op % 7 {
            0 => {
                pvec = pvec.push_back(val);
                std_vec.push(val);
            },
            1 => {
                pvec = pvec.push_front(val);
                std_vec.insert(0, val);
            },
            2 => {
                let p_pop = pvec.pop_back().map(|(v, x)| {
                    pvec = v;
                    x
                });
                let s_pop = std_vec.pop();
                assert_eq!(p_pop, s_pop, "Step {step} pop_back mismatch");
            },
            3 => {
                if !std_vec.is_empty() {
                    let idx = raw_idx % std_vec.len();
                    pvec = pvec.update(idx, val);
                    std_vec[idx] = val;
                }
            },
            4 => {
                if !std_vec.is_empty() {
                    let idx = raw_idx % std_vec.len();
                    assert_eq!(
                        pvec.get(idx),
                        std_vec.get(idx),
                        "Step {step} get mismatch at {idx}"
                    );
                }
            },
            5 => {
                if !std_vec.is_empty() {
                    let idx = raw_idx % (std_vec.len() + 1);
                    let (left, right) = pvec.split_at(idx);
                    assert_eq!(left.len(), idx, "Step {step} split_at left.len()");
                    assert_eq!(
                        right.len(),
                        std_vec.len() - idx,
                        "Step {step} split_at right.len()"
                    );
                    assert_eq!(
                        left.to_vec(),
                        std_vec[..idx],
                        "Step {step} left content mismatch"
                    );
                    assert_eq!(
                        right.to_vec(),
                        std_vec[idx..],
                        "Step {step} right content mismatch"
                    );
                    pvec = left.concat(&right);
                    assert_eq!(
                        pvec.to_vec(),
                        std_vec,
                        "Step {step} concat content mismatch"
                    );
                }
            },
            6 => {
                let p_pop = pvec.pop_front().map(|(v, x)| {
                    pvec = v;
                    x
                });
                let s_pop = if std_vec.is_empty() {
                    None
                } else {
                    Some(std_vec.remove(0))
                };
                assert_eq!(p_pop, s_pop, "Step {step} pop_front mismatch");
            },
            _ => unreachable!(),
        }
    }
    assert_eq!(pvec.to_vec(), std_vec);
}

#[quickcheck]
fn qc_pvec_differential(initial_size: usize, operations: Vec<(u8, usize, i32)>) -> TestResult {
    // Allows testing both small inline/height-1 vectors and large height-2 vectors (up to 3500)
    let init_len = initial_size % 3500;
    let mut pvec: PersistentVector<i32> = (0..init_len as i32).collect();
    let mut std_vec: Vec<i32> = (0..init_len as i32).collect();

    for (op, raw_idx, val) in operations.into_iter().take(100) {
        match op % 7 {
            0 => {
                // push_back
                pvec = pvec.push_back(val);
                std_vec.push(val);
            },
            1 => {
                // push_front
                pvec = pvec.push_front(val);
                std_vec.insert(0, val);
            },
            2 => {
                // pop_back
                let p_pop = pvec.pop_back().map(|(v, x)| {
                    pvec = v;
                    x
                });
                let s_pop = std_vec.pop();
                if p_pop != s_pop {
                    return TestResult::failed();
                }
            },
            3 => {
                // update
                if !std_vec.is_empty() {
                    let idx = raw_idx % std_vec.len();
                    pvec = pvec.update(idx, val);
                    std_vec[idx] = val;
                }
            },
            4 => {
                // get
                if !std_vec.is_empty() {
                    let idx = raw_idx % std_vec.len();
                    if pvec.get(idx) != std_vec.get(idx) {
                        return TestResult::failed();
                    }
                }
            },
            5 => {
                // split_at and concat
                if !std_vec.is_empty() {
                    let idx = raw_idx % (std_vec.len() + 1);
                    let (left, right) = pvec.split_at(idx);
                    if left.len() != idx || right.len() != std_vec.len() - idx {
                        return TestResult::failed();
                    }
                    if left.to_vec() != std_vec[..idx] || right.to_vec() != std_vec[idx..] {
                        return TestResult::failed();
                    }
                    pvec = left.concat(&right);
                }
            },
            6 => {
                // pop_front
                let p_pop = pvec.pop_front().map(|(v, x)| {
                    pvec = v;
                    x
                });
                let s_pop = if std_vec.is_empty() {
                    None
                } else {
                    Some(std_vec.remove(0))
                };
                if p_pop != s_pop {
                    return TestResult::failed();
                }
            },
            _ => unreachable!(),
        }
    }

    TestResult::from_bool(pvec.to_vec() == std_vec)
}
