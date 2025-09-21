#[cfg(test)]
mod tests {
    use rustica::utils::categorical_utils::*;

    #[test]
    fn test_map_option() {
        assert_eq!(map_option(Some(1), |x| x + 1), Some(2));
        assert_eq!(map_option(None::<i32>, |x| x + 1), None);
    }

    #[test]
    fn test_map_result() {
        assert_eq!(map_result(Ok::<i32, &str>(1), |x| x + 1), Ok(2));
        assert_eq!(map_result(Err("error"), |x: i32| x + 1), Err("error"));
    }

    #[test]
    fn test_bimap_result() {
        assert_eq!(
            bimap_result(Ok(1), |x| x + 1, |e: &str| e.to_uppercase()),
            Ok(2)
        );
        assert_eq!(
            bimap_result(Err("error"), |x: i32| x + 1, |e| e.to_uppercase()),
            Err("ERROR".to_string())
        );
    }

    #[test]
    fn test_flat_map_option() {
        let safe_divide = |x, y| if y != 0 { Some(x / y) } else { None };
        assert_eq!(flat_map_option(Some(20), |x| safe_divide(x, 4)), Some(5));
        assert_eq!(flat_map_option(Some(10), |x| safe_divide(x, 0)), None);
        assert_eq!(flat_map_option(None::<i32>, |x| Some(x)), None);
    }

    #[test]
    fn test_flat_map_result() {
        let parse_int = |s: &str| s.parse::<i32>().map_err(|_| "parse error");
        assert_eq!(flat_map_result(Ok("42"), parse_int), Ok(42));
        assert_eq!(
            flat_map_result(Err("initial error"), parse_int),
            Err("initial error")
        );
    }

    #[test]
    fn test_compose() {
        let add_one = |x: i32| x + 1;
        let double = |x: i32| x * 2;
        let composed = compose(double, add_one);
        assert_eq!(composed(5), 12); // (5 + 1) * 2
    }

    #[test]
    fn test_pipe() {
        let add_one = |x: i32| x + 1;
        let double = |x: i32| x * 2;
        let to_string = |x: i32| x.to_string();
        let pipeline = pipe(pipe(add_one, double), to_string);
        assert_eq!(pipeline(3), "8"); // (3 + 1) * 2 = "8"
    }

    #[test]
    fn test_flip() {
        let subtract = |x: i32, y: i32| x - y;
        let flipped_subtract = flip(subtract);

        assert_eq!(subtract(10, 3), 7); // 10 - 3 = 7
        assert_eq!(flipped_subtract(10, 3), -7); // 3 - 10 = -7

        let divide = |x: f64, y: f64| x / y;
        let flipped_divide = flip(divide);
        assert_eq!(flipped_divide(2.0, 8.0), 4.0); // 8 / 2 = 4
    }

    #[test]
    fn test_filter_map_collect() {
        let numbers = vec!["1", "not_a_number", "3", "4"];
        let parsed = filter_map_collect(numbers.iter(), |s| s.parse::<i32>().ok());
        assert_eq!(parsed, vec![1, 3, 4]);
    }

    #[test]
    fn test_sequence_options() {
        let all_some = vec![Some(1), Some(2), Some(3)];
        assert_eq!(sequence_options(all_some), Some(vec![1, 2, 3]));

        let has_none = vec![Some(1), None, Some(3)];
        assert_eq!(sequence_options(has_none), None);

        let empty: Vec<Option<i32>> = vec![];
        assert_eq!(sequence_options(empty), Some(vec![]));
    }

    #[test]
    fn test_sequence_results() {
        let all_ok: Vec<Result<i32, &str>> = vec![Ok(1), Ok(2), Ok(3)];
        assert_eq!(sequence_results(all_ok), Ok(vec![1, 2, 3]));

        let has_err: Vec<Result<i32, &str>> = vec![Ok(1), Err("error"), Ok(3)];
        assert_eq!(sequence_results(has_err), Err("error"));
    }

    #[test]
    fn test_functor_laws() {
        // Identity law for map_option
        let original = Some(42);
        assert_eq!(map_option(original, |x| x), original);

        // Composition law for map_option
        let f = |x: i32| x + 1;
        let g = |x: i32| x * 2;
        let option = Some(5);

        let result1 = map_option(map_option(option, f), g);
        let result2 = map_option(option, |x| g(f(x)));
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_monad_laws() {
        // Left identity law for flat_map_option
        let f = |x: i32| if x > 0 { Some(x * 2) } else { None };
        let x = 5;
        assert_eq!(flat_map_option(Some(x), &f), f(x));

        // Right identity law for flat_map_option
        let option = Some(42);
        assert_eq!(flat_map_option(option, Some), option);
    }
}
