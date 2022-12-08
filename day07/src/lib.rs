//! Solutions to [Advent of Code 2022 Day 7](https://adventofcode.com/2022/day/7).

use std::collections::HashMap;
use std::io;
use std::num::ParseIntError;
use std::path::PathBuf;

use once_cell::sync::OnceCell;
use regex::Regex;
use thiserror::Error;

macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: OnceCell<Regex> = OnceCell::new();
        RE.get_or_init(|| Regex::new($re).unwrap())
    }};
}

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// Terminal output contains an unrecognized command.
    #[error("Terminal output contains an unrecognized command: '{0}'")]
    UnrecognizedCommand(String),

    /// Terminal output contains unparsable `ls` output.
    #[error("Terminal output contains unparseable line: '{0}'")]
    BadListing(String),

    /// Error parsing file size
    #[error("Error parsing file size")]
    ParseInt(#[from] ParseIntError),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

/// Filesystem traversal commands.
#[derive(Debug, Clone)]
pub enum Command {
    /// Change the current directory.
    Cd(CdArg),

    /// List the entries of the current directory.
    Ls(Vec<Listing>),
}

/// An argument to the `cd` command.
#[derive(Debug, Clone)]
pub enum CdArg {
    /// Ascend to the filesystem root directory.
    Root,

    /// Ascend to the parent directory.
    Parent,

    /// Descent to a named child directory.
    Child(String),
}

/// Directory listing output.
#[derive(Debug, Clone)]
pub enum Listing {
    /// A file size and name.
    File(usize, String),

    /// A directory name.
    Directory(String),
}

/// Parses the terminal display of a file system walk into a vector of [`Command`]s.
///
/// # Errors
///
/// Returns [`Error`] for any parse errors encountered, such as unrecognized commands or command
/// output.
pub fn parse_input(s: &str) -> Result<Vec<Command>> {
    let prompt_regex = regex!(r"(?m)(^|\n)\$ ");
    let command_regex = regex!(r"(?sm)^(cd (?P<arg>.*))|(ls(?P<output>.*))$");

    let mut commands = Vec::new();
    for block in prompt_regex.split(s) {
        if block.trim().is_empty() {
            continue;
        }
        let caps = command_regex
            .captures(block)
            .ok_or_else(|| Error::UnrecognizedCommand(block.into()))?;
        if let Some(arg) = caps.name("arg") {
            let command = parse_cd(arg.as_str());
            commands.push(command);
        }
        if let Some(output) = caps.name("output") {
            let command = parse_ls_output(output.as_str())?;
            commands.push(command);
        }
    }
    Ok(commands)
}

fn parse_cd(s: &str) -> Command {
    let cd_arg = match s {
        "/" => CdArg::Root,
        ".." => CdArg::Parent,
        s => CdArg::Child(s.into()),
    };
    Command::Cd(cd_arg)
}

fn parse_ls_output(output: &str) -> Result<Command> {
    let listing_regex = regex!(r"(dir (?P<dirname>.*))|((?P<size>[[:digit:]]*) (?P<filename>.*))");
    let mut listings = Vec::new();
    for line in output.lines() {
        if let Some(caps) = listing_regex.captures(line) {
            if let Some(name) = caps.name("dirname") {
                let listing = Listing::Directory(name.as_str().into());
                listings.push(listing);
            } else {
                // If we didn't match the cd command, then we must have matched the ls
                // command.
                let size = caps
                    .name("size")
                    .expect("file file listings have a size")
                    .as_str()
                    .parse()?;
                let name = caps
                    .name("filename")
                    .expect("file listings have a name")
                    .as_str()
                    .into();
                let listing = Listing::File(size, name);
                listings.push(listing);
            }
        }
    }
    let command = Command::Ls(listings);
    Ok(command)
}

// Note on converting the input to a tree
// ======================================
//
// The problem does not specify whether the directory walk represented in the puzzle input will
// only visit any particular directory once.  We aim to contruct a tree representing the file
// system, but we need to build it bottom-up.  To deal with the possibility that the walk in the
// input revisits some nodes, we first construct an extrinsic view of the filesystem mapping the
// absolute paths of directories to a vector of struct `DirEntry`s.  Then we perform a depth-first
// traversal of the filesystem via this map to construct an intrinsic view, where a node is either
// a `File::File` (leaf) or a `File::Directory`, the latter holding a map from names to `File`s.
// The nested ownership is contructed bottom-up via the depth-first tree traversal.

#[derive(Debug, Clone)]
pub struct DirEntry {
    name: String,
    kind: FileKind,
    size: usize,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum FileKind {
    File,
    Directory,
}

/// An entry in the file system.
#[derive(Debug, Clone)]
pub enum File {
    /// A regular file stores its size.
    File(usize),

    /// A directory maps names to its child filesystem entries.
    Directory(HashMap<String, File>),
}

/// Reconstruct the filesystem tree from a directory walk.
#[must_use]
pub fn build_fs_tree(commands: &[Command]) -> File {
    // First build a map from the absolute paths of directories to vectors of their entries.
    let map = build_fs_map(commands);

    // Now peform a depth-first walk of the tree represented by the filesystem and build an actual
    // tree structure.
    let mut cwd = PathBuf::from("/");
    let root = walk_map(&map, &mut cwd);
    File::Directory(root)
}

/// Build an extrinsic filesystem map from a list of traversal commands.
fn build_fs_map(commands: &[Command]) -> HashMap<PathBuf, Vec<DirEntry>> {
    let mut map = HashMap::new();
    let mut cwd = PathBuf::new();
    for command in commands {
        match command {
            Command::Cd(arg) => {
                match arg {
                    CdArg::Root => cwd.push("/"),
                    CdArg::Parent => {
                        let _ = cwd.pop();
                    }
                    CdArg::Child(name) => cwd.push(name),
                };
            }
            Command::Ls(listings) => {
                let entries: Vec<_> = listings
                    .iter()
                    .map(|listing| match listing {
                        Listing::File(size, name) => DirEntry {
                            name: name.to_string(),
                            kind: FileKind::File,
                            size: *size,
                        },
                        Listing::Directory(name) => DirEntry {
                            name: name.to_string(),
                            kind: FileKind::Directory,
                            size: 0,
                        },
                    })
                    .collect();
                map.insert(cwd.clone(), entries);
            }
        }
    }
    map
}

fn walk_map(map: &HashMap<PathBuf, Vec<DirEntry>>, cwd: &mut PathBuf) -> HashMap<String, File> {
    let mut dirmap = HashMap::new();
    for entry in map.get(cwd).unwrap() {
        match entry.kind {
            FileKind::File => {
                let file = File::File(entry.size);
                dirmap.insert(entry.name.clone(), file);
            }
            FileKind::Directory => {
                cwd.push(&entry.name);
                let child = walk_map(map, cwd);
                cwd.pop();
                let dir = File::Directory(child);
                dirmap.insert(entry.name.clone(), dir);
            }
        }
    }
    dirmap
}

/// Returns the path, kind, and size of every entry in the file system.
///
/// For directories, the size is the total size, summing the sizes of all files and subdirectories.
#[must_use]
pub fn find_sizes(root: &File) -> Vec<(PathBuf, FileKind, usize)> {
    let mut items = Vec::new();
    let mut path = PathBuf::from("/");
    find_sizes_inner(root, &mut path, &mut items);
    items
}

fn find_sizes_inner(
    file: &File,
    path: &mut PathBuf,
    items: &mut Vec<(PathBuf, FileKind, usize)>,
) -> usize {
    match file {
        File::File(size) => {
            items.push((path.clone(), FileKind::File, *size));
            *size
        }
        File::Directory(map) => {
            let mut size = 0;
            for (name, file) in map {
                path.push(name);
                size += find_sizes_inner(file, path, items);
                path.pop();
            }
            items.push((path.clone(), FileKind::Directory, size));
            size
        }
    }
}

/// Returns the some of the total sizes of directories whose total size does not exceed 100000.
#[must_use]
pub fn solve_part1(root: &File) -> usize {
    find_sizes(root)
        .into_iter()
        .filter_map(|(_path, kind, size)| {
            if kind == FileKind::Directory && size < 100_000 {
                Some(size)
            } else {
                None
            }
        })
        .sum()
}

/// Returns the total size of the smallest directory that can be removed to free sufficient space.
#[must_use]
pub fn solve_part2(root: &File) -> Option<usize> {
    let total_available = 70_000_000;
    let required = 30_000_000;
    let items = find_sizes(root);
    let used = items.last().map_or(0, |(_, _, size)| *size);
    if used + required < total_available {
        Some(0)
    } else {
        items
            .into_iter()
            .filter_map(|(_path, kind, size)| {
                if kind == FileKind::Directory && size >= used + required - total_available {
                    Some(size)
                } else {
                    None
                }
            })
            .min()
    }
}

// Just some exercises for walking the intrinsic view of the file system.

pub fn walk_fs(root: &File) {
    let mut path = PathBuf::from("/");
    walk_fs_inner(root, &mut path);
}

pub fn walk_fs_inner(file: &File, path: &mut PathBuf) {
    match file {
        File::File(size) => {
            println!("{size:8}  {}", path.display());
        }
        File::Directory(map) => {
            for (name, file) in map {
                path.push(name);
                walk_fs_inner(file, path);
                path.pop();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let commands = parse_input(&input)?;
        let root = build_fs_tree(&commands);
        let size = solve_part1(&root);
        assert_eq!(size, 95437);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let commands = parse_input(&input)?;
        let root = build_fs_tree(&commands);
        let size = solve_part1(&root);
        assert_eq!(size, 1743217);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let commands = parse_input(&input)?;
        let root = build_fs_tree(&commands);
        let size = solve_part2(&root);
        assert_eq!(size, Some(24933642));
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let commands = parse_input(&input)?;
        let root = build_fs_tree(&commands);
        let size = solve_part2(&root);
        assert_eq!(size, Some(8319096));
        Ok(())
    }
}
