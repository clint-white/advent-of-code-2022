//! Solutions to [Advent of Code 2022 Day 6](https://adventofcode.com/2022/day/6).

use std::hash::Hash;

use hashbag::HashBag;

/// Finds the first occurrence of `n` consecutive elements which are all unique.
///
/// Returns `None` if there is no such window.
///
/// # Examples
///
/// ```
/// use day06::find_unique_window;
///
/// let xs = b"bvwbjplbgvbhsrlpgdmjqwftvncz";
/// let pos = find_unique_window(xs.as_slice(), 4);
/// assert_eq!(pos, Some(1));
///
/// let xs = b"nppdvjthqldpwncqszvftbrmjlhg";
/// let pos = find_unique_window(xs.as_slice(), 4);
/// assert_eq!(pos, Some(2));
///
/// let xs = b"nznrnfrfntjfmvfwmzdfjlvtqnbhcprsg";
/// let pos = find_unique_window(xs.as_slice(), 4);
/// assert_eq!(pos, Some(6));
///
/// let xs = b"zcfzfwzzqfrljwzlrfnpqdbhtmscgvjw";
/// let pos = find_unique_window(xs.as_slice(), 4);
/// assert_eq!(pos, Some(7));
///
/// let xs = b"zcfzfwzzqfzfzfwzzqfzfzfwzzqfzfzfwzzqfzfzfwzzqf";
/// let pos = find_unique_window(xs.as_slice(), 4);
/// assert_eq!(pos, None);
/// ```
pub fn find_unique_window<T>(xs: &[T], n: usize) -> Option<usize>
where
    T: Hash + Eq,
{
    if n == 0 {
        return Some(0);
    }
    let mut items = xs.iter();
    let mut bag: HashBag<_> = items.by_ref().take(n - 1).collect();
    for ((i, old), new) in xs.iter().enumerate().zip(items) {
        bag.insert(new);
        if bag.set_len() == n {
            return Some(i);
        }
        bag.remove(old);
        debug_assert!(bag.len() == n - 1);
    }
    None
}

/// Returns the number of bytes up to and including the first occurrence of 4 consecutive unique
/// bytes.
#[must_use]
pub fn solve_part1(bytes: &[u8]) -> Option<usize> {
    find_unique_window(bytes, 4).map(|k| k + 4)
}

/// Returns the number of bytes up to and including the first occurrence of 14 consecutive unique
/// bytes.
#[must_use]
pub fn solve_part2(bytes: &[u8]) -> Option<usize> {
    find_unique_window(bytes, 14).map(|k| k + 14)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() {
        let xs = b"bvwbjplbgvbhsrlpgdmjqwftvncz";
        let pos = solve_part1(xs.as_slice());
        assert_eq!(pos, Some(5));

        let xs = b"nppdvjthqldpwncqszvftbrmjlhg";
        let pos = solve_part1(xs.as_slice());
        assert_eq!(pos, Some(6));

        let xs = b"nznrnfrfntjfmvfwmzdfjlvtqnbhcprsg";
        let pos = solve_part1(xs.as_slice());
        assert_eq!(pos, Some(10));

        let xs = b"zcfzfwzzqfrljwzlrfnpqdbhtmscgvjw";
        let pos = solve_part1(xs.as_slice());
        assert_eq!(pos, Some(11));
    }

    #[test]
    fn test_part1_input() -> io::Result<()> {
        let input = fs::read("data/input")?;
        let pos = solve_part1(&input);
        assert_eq!(pos, Some(1140));
        Ok(())
    }

    #[test]
    fn test_part2_example() {
        let xs = b"mjqjpqmgbljsphdztnvjfqwrcgsmlb";
        let pos = solve_part2(xs.as_slice());
        assert_eq!(pos, Some(19));

        let xs = b"bvwbjplbgvbhsrlpgdmjqwftvncz";
        let pos = solve_part2(xs.as_slice());
        assert_eq!(pos, Some(23));

        let xs = b"nppdvjthqldpwncqszvftbrmjlhg";
        let pos = solve_part2(xs.as_slice());
        assert_eq!(pos, Some(23));

        let xs = b"nznrnfrfntjfmvfwmzdfjlvtqnbhcprsg";
        let pos = solve_part2(xs.as_slice());
        assert_eq!(pos, Some(29));

        let xs = b"zcfzfwzzqfrljwzlrfnpqdbhtmscgvjw";
        let pos = solve_part2(xs.as_slice());
        assert_eq!(pos, Some(26));
    }

    #[test]
    fn test_part2_input() -> io::Result<()> {
        let input = fs::read("data/input")?;
        let pos = solve_part2(&input);
        assert_eq!(pos, Some(3495));
        Ok(())
    }
}
