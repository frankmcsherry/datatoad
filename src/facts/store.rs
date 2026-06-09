//! On-disk persistence for fact collections.
//!
//! ```text
//! <dir>/<name>/identity/
//!   lsm_<i>/
//!     layer_<j>.bin
//! ```
//!
//! One file per trie column; each file holds a single columnar-encoded
//! `Stash<Lists<Terms>, Bytes>`. The `recent` slot (if present) is written
//! as the trailing `lsm_<i>` directory.


use std::path::Path;
use std::rc::Rc;

use crate::facts::trie::Layer;
use crate::facts::{FactCollection, FactSet, Lists, Terms};

/// Writes `facts.stable` and `facts.recent` under `<dir>/<name>/identity/`.
/// Returns the number of layer directories written. The write is staged
/// through a sibling directory and renamed into place; failures leave any
/// existing `identity/` unchanged.
pub fn save_identity(name: &str, dir: &Path, facts: &FactSet<FactCollection>) -> std::io::Result<usize> {
    let base = dir.join(name);
    std::fs::create_dir_all(&base)?;

    let final_root = base.join("identity");
    let suffix = format!(
        "{}.{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0),
    );
    let staging = base.join(format!(".identity.staging.{suffix}"));
    let trash = base.join(format!(".identity.trash.{suffix}"));

    let _ = std::fs::remove_dir_all(&staging);
    std::fs::create_dir_all(&staging)?;

    let result = (|| -> std::io::Result<usize> {
        let mut index = 0;
        for layer in facts.stable.contents() {
            save_forest(&staging.join(format!("lsm_{:03}", index)), layer)?;
            index += 1;
        }
        if let Some(recent) = facts.recent.as_ref() {
            save_forest(&staging.join(format!("lsm_{:03}", index)), recent)?;
            index += 1;
        }
        Ok(index)
    })();

    let index = match result {
        Ok(n) => n,
        Err(e) => {
            // Don't leave a half-written staging dir behind on failure.
            let _ = std::fs::remove_dir_all(&staging);
            return Err(e);
        }
    };

    // Commit: move old identity aside, move staging in, delete old.
    let had_prior = final_root.exists();
    if had_prior {
        std::fs::rename(&final_root, &trash)?;
    }
    if let Err(e) = std::fs::rename(&staging, &final_root) {
        // Best-effort rollback: try to put the old identity back so the user
        // isn't left with no identity dir at all.
        if had_prior {
            let _ = std::fs::rename(&trash, &final_root);
        }
        let _ = std::fs::remove_dir_all(&staging);
        return Err(e);
    }
    if had_prior {
        let _ = std::fs::remove_dir_all(&trash);
    }
    Ok(index)
}

fn save_forest(dir: &Path, forest: &FactCollection) -> std::io::Result<()> {
    std::fs::create_dir_all(dir)?;
    for j in 0..forest.arity() {
        save_layer(&dir.join(format!("layer_{:03}.bin", j)), forest.layer(j))?;
    }
    Ok(())
}

fn save_layer(path: &Path, layer: &Layer<Terms>) -> std::io::Result<()> {
    let mut f = std::fs::File::create(path)?;
    layer
        .list
        .write_bytes(&mut f)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("write_bytes: {e:?}")))
}

/// Inverse of [`save_identity`]. Returns the recovered LSM layers, one
/// `Forest<Terms>` per `lsm_<i>` directory, sorted by directory name.
pub fn load_identity(name: &str, dir: &Path) -> std::io::Result<Vec<FactCollection>> {
    let root = dir.join(name).join("identity");
    if !root.exists() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("identity directory not found: {}", root.display()),
        ));
    }

    let mut lsm_dirs: Vec<std::path::PathBuf> = std::fs::read_dir(&root)?
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    lsm_dirs.sort();

    let mut out = Vec::with_capacity(lsm_dirs.len());
    for lsm_dir in lsm_dirs {
        out.push(load_forest(&lsm_dir)?);
    }
    Ok(out)
}

fn load_forest(dir: &Path) -> std::io::Result<FactCollection> {
    let mut layer_files: Vec<std::path::PathBuf> = std::fs::read_dir(dir)?
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_file() && p.extension().is_some_and(|ext| ext == "bin"))
        .collect();
    layer_files.sort();

    let mut layers: Vec<Rc<Layer<Terms>>> = Vec::with_capacity(layer_files.len());
    for layer_file in layer_files {
        let list = mmap_layer(&layer_file)?;
        layers.push(Rc::new(Layer { list }));
    }
    layers.try_into().map_err(|_| std::io::Error::new(
        std::io::ErrorKind::InvalidData,
        "loaded layers fail Forest::try_from invariants",
    ))
}

/// mmap a layer file as a `Stash::Bytes`. Empty files become an empty
/// `Stash::Typed` since `mmap` requires `len > 0`.
fn mmap_layer(path: &Path) -> std::io::Result<columnar::bytes::stash::Stash<Lists<Terms>, timely_bytes::arc::Bytes>> {
    let file = std::fs::File::open(path)?;
    let len = file.metadata()?.len();
    if len == 0 {
        return Ok(columnar::bytes::stash::Stash::Typed(Default::default()));
    }
    // SAFETY: map_copy is private (writes don't propagate back) and we never
    // write through the mapping; the only path that would (`make_typed`)
    // replaces the variant before any byte is touched.
    let mmap = unsafe { memmap2::MmapOptions::new().map_copy(&file)? };
    let bytes = timely_bytes::arc::BytesMut::from(mmap).freeze();
    columnar::bytes::stash::Stash::try_from_bytes(bytes)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
}
