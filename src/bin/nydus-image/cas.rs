use anyhow::Context;
use nydus_storage::device::BlobInfo;
use rusqlite::{Connection, Transaction};
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::convert::TryInto;
use std::error::Error;
use std::fs::{self, OpenOptions};
use std::hash::Hash;
use std::io::SeekFrom;
use std::mem::size_of;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::Instant;

use rafs::metadata::layout::v5::{
    rafsv5_align, RafsV5BlobTable, RafsV5ChunkInfo, RafsV5ExtBlobEntry, RafsV5InodeTable,
    RafsV5SuperBlock, RafsV5XAttrsTable,
};
use rafs::metadata::layout::v6::{
    align_offset, RafsV6BlobTable, RafsV6Device, RafsV6InodeChunkAddr, RafsV6SuperBlock,
    RafsV6SuperBlockExt, EROFS_BLOCK_SIZE, EROFS_INODE_SLOT_SIZE,
};
use rafs::metadata::{RafsMode, RafsStore, RafsSuper};
use rafs::{RafsIoReader, RafsIoWrite};

use crate::core::context::{ArtifactFileWriter, ArtifactStorage, ArtifactWriter};
use crate::core::node::ChunkWrapper;
use crate::core::tree::Tree;

use nydus_utils::digest::RafsDigest;

lazy_static::lazy_static! {
    pub static ref CAS_MGR: CasMgr = CasMgr::new();
}

#[derive(Default)]
pub struct CasMgr {
    state: Mutex<Option<CasStateMgr>>,
}

impl CasMgr {
    pub fn new() -> Self {
        Self {
            state: Mutex::new(None),
        }
    }

    pub fn init(&self, dirpath: impl AsRef<Path>) -> Result<(), Box<dyn Error>> {
        let cas = CasStateMgr::new(dirpath)?;
        self.state.lock().unwrap().replace(cas);
        Ok(())
    }

    #[inline]
    fn get_state(&self) -> MutexGuard<Option<CasStateMgr>> {
        self.state.lock().unwrap()
    }

    pub fn add_bootstrap(&self, file: impl AsRef<Path>, mnt: impl AsRef<Path>) -> PathBuf {
        info!("cas: add bootstrap {:?} {:?}", file.as_ref(), mnt.as_ref());
        self.get_state().as_mut().unwrap().add_bootstrap(file, mnt)
    }

    #[allow(dead_code)]
    pub fn remove_bootstrap(&self, mnt: impl AsRef<Path>) {
        info!("cas: remove bootstrap {:?}", mnt.as_ref());
        self.get_state().as_mut().unwrap().remove_bootstrap(mnt)
    }

    pub fn _mark_data_ready(&self, blob_id: &str, start: u64, len: u64) {
        info!("cas: mark {:?} {:?} for {:?}", start, len, blob_id);
    }

    pub fn _gc(&self) {
        todo!()
    }
}

struct BootstrapObject {
    source: PathBuf,
    cache: PathBuf,
    ref_count: AtomicU32,
}

#[allow(dead_code)]
struct CasStateMgr {
    dir: PathBuf,
    path_map: HashMap<PathBuf, Arc<BootstrapObject>>,
    mnt_map: HashMap<PathBuf, Arc<BootstrapObject>>,
    blobs: HashMap<String, Arc<BlobInfo>>,
    db: CasDbMgr,
}

impl CasStateMgr {
    fn new(dirpath: impl AsRef<Path>) -> Result<Self, Box<dyn Error>> {
        info!("cas: CasStateMgr dir {:?}", dirpath.as_ref());
        Ok(CasStateMgr {
            //todo: pre cache dir
            dir: dirpath.as_ref().to_path_buf(),
            path_map: HashMap::new(),
            mnt_map: HashMap::new(),
            blobs: HashMap::new(),
            //chunks: HashMap::new(),
            db: CasDbMgr::new(dirpath)?,
        })
    }

    fn rebuild_bootstrap(&mut self, o: Arc<BootstrapObject>) -> Result<(), Box<dyn Error>> {
        fs::copy(o.source.as_path(), o.cache.as_path()).unwrap();
        debug!("cas: bootstrap {:?} cache to {:?}", o.source, o.cache);

        let sb = RafsSuper::load_from_metadata(&o.cache, RafsMode::Direct, true)?;
        let tree = Tree::from_bootstrap(&sb, &mut ())?;

        let mut blob_infos = sb.superblock.get_blob_infos();
        for blob in &blob_infos {
            //info!("cas: blob {:?}", blob);
            let sblob = serde_json::to_string(blob).unwrap();
            self.db.add_blob(blob.blob_id(), &sblob);
            if self.blobs.get(blob.blob_id()).is_none() {
                self.blobs.insert(blob.blob_id().to_owned(), blob.clone());
            }
        }
        let mut curr_blob_idx = blob_infos.len() - 1;
        let mut new_blobs: HashMap<String, usize> = HashMap::new();
        let mut cache_chunks: HashMap<RafsDigest, Option<ChunkWrapper>> = HashMap::new();

        let storage = ArtifactStorage::SingleFile(PathBuf::from(&o.cache));
        let mut writer = Box::new(ArtifactFileWriter(ArtifactWriter::new(storage, true)?))
            as Box<dyn RafsIoWrite>;
        let file = OpenOptions::new().read(true).write(false).open(&o.cache)?;
        let mut reader = Box::new(file) as RafsIoReader;

        if sb.meta.is_v5() {
            let mut inodes_table = RafsV5InodeTable::new(sb.meta.inode_table_entries as usize);
            reader.seek_to_offset(sb.meta.inode_table_offset)?;
            inodes_table.load(&mut reader)?;

            let unit = size_of::<RafsV5ChunkInfo>() as u64;
            //tree iter, rewrite chunk
            tree.iterate(&mut |node| {
                let v5_offset = inodes_table.get(node.src_ino).unwrap();
                let mut chunk_ofs = (v5_offset + node.inode.inode_size() as u32) as u64;
                if node.inode.has_xattr() {
                    chunk_ofs +=
                        (size_of::<RafsV5XAttrsTable>() + node.xattrs.aligned_size_v5()) as u64;
                }
                for chunk in &node.chunks {
                    //debug!("cas: chunk {}", chunk);
                    let old_id = blob_infos[chunk.inner.blob_index() as usize].blob_id();
                    let chunk_id = chunk.inner.id();
                    let chunk_w_o = match cache_chunks.get(chunk_id) {
                        Some(c) => c.clone(),
                        None => {
                            let (new_id, cis) = self.db.add_chunk(&chunk.inner, old_id, 0);
                            if new_id != *old_id {
                                let blob_idx = match new_blobs.get(&new_id) {
                                    Some(i) => i.to_owned(),
                                    None => {
                                        curr_blob_idx += 1;
                                        //just alloc idx here, dump when all chunk check done
                                        new_blobs.insert(new_id.clone(), curr_blob_idx);
                                        curr_blob_idx
                                    }
                                };
                                let mut chunk_w =
                                    serde_json::from_str::<ChunkWrapper>(&cis.unwrap()).unwrap();
                                chunk_w.set_blob_index(blob_idx as u32);
                                cache_chunks.insert(*chunk_w.id(), Some(chunk_w.clone()));
                                Some(chunk_w)
                            } else {
                                cache_chunks.insert(*chunk_id, None);
                                None
                            }
                        }
                    };

                    if let Some(chunk_w) = chunk_w_o {
                        writer
                            .seek_offset(chunk_ofs)
                            .context("failed seek chunk offset")
                            .unwrap();
                        chunk_w
                            .store(writer.as_mut())
                            .context("failed to dump chunk info to bootstrap")
                            .unwrap();
                    }
                    chunk_ofs += unit;
                }
                true
            })?;

            if !new_blobs.is_empty() {
                let mut new_blobs_vec: Vec<(&String, &usize)> = new_blobs.iter().collect();
                new_blobs_vec.sort_by(|a, b| a.1.cmp(b.1));
                for idx in new_blobs_vec {
                    let blob_info = match self.blobs.get(idx.0) {
                        Some(bi) => bi,
                        None => {
                            let bis = self.db.get_blob(idx.0).unwrap();
                            let bi = serde_json::from_str::<BlobInfo>(&bis).unwrap();
                            self.blobs.insert(bi.blob_id().to_owned(), Arc::new(bi));
                            self.blobs.get(idx.0).unwrap()
                        }
                    };
                    let mut blob = BlobInfo::from(blob_info);
                    blob.set_blob_index(*idx.1 as u32);
                    //debug!("cas: rw blob {:?}", blob);
                    blob_infos.push(Arc::new(blob));
                }
            }
            let blob_table = RafsV5BlobTable::from(blob_infos);
            reader.seek_to_offset(0)?;
            let mut sb_v5 = RafsV5SuperBlock::new();
            reader.read_exact(sb_v5.as_mut())?;
            let ori_blob_table_ofs = sb_v5.blob_table_offset();
            let ori_blob_table_size = sb_v5.blob_table_size();
            let ori_ext_blob_table_size = rafsv5_align(
                size_of::<RafsV5ExtBlobEntry>() * sb_v5.extended_blob_table_entries() as usize,
            );
            let blob_table_size = blob_table.size() as u32;
            let (blob_table_ofs, ext_blob_table_ofs) =
                if blob_table_size > ori_blob_table_size + ori_ext_blob_table_size as u32 {
                    let blob_table_ofs = writer
                        .seek_to_end()
                        .context("failed to seek to bootstrap's end for devtable")?;
                    let ext_blob_table_ofs = align_offset(
                        blob_table_ofs + blob_table_size as u64,
                        EROFS_BLOCK_SIZE as u64,
                    );
                    (blob_table_ofs, ext_blob_table_ofs)
                } else {
                    let ext_blob_table_ofs = writer
                        .seek_to_end()
                        .context("failed to seek to bootstrap's end for blob table")?;
                    (ori_blob_table_ofs, ext_blob_table_ofs)
                };
            //write sb
            sb_v5.set_blob_table_offset(blob_table_ofs as u64);
            sb_v5.set_blob_table_size(blob_table_size as u32);
            sb_v5.set_extended_blob_table_offset(ext_blob_table_ofs as u64);
            sb_v5.set_extended_blob_table_entries(u32::try_from(blob_table.extended.entries())?);
            writer.seek(SeekFrom::Start(0))?;
            sb_v5
                .store(writer.as_mut())
                .context("failed to store superblock")?;
            //rewrite blob table
            writer
                .seek_offset(blob_table_ofs)
                .context("failed seek for extended blob table offset")?;
            blob_table
                .store(writer.as_mut())
                .context("failed to store blob table")?;
            writer
                .seek_offset(ext_blob_table_ofs)
                .context("failed seek for extended blob table offset")?;
            blob_table
                .store_extended(writer.as_mut())
                .context("failed to store extended blob table")?;
            writer.finalize(Some(String::default()))?;
        } else if sb.meta.is_v6() {
            let unit = size_of::<RafsV6InodeChunkAddr>() as u64;

            tree.iterate(&mut |node| {
                //TODO: fix node.v6_offset
                let v6_offset = sb.meta.meta_blkaddr as u64 * EROFS_BLOCK_SIZE
                    + node.src_ino * EROFS_INODE_SLOT_SIZE as u64;
                let mut chunk_ofs =
                    align_offset(v6_offset + node.v6_size_with_xattr() as u64, unit);

                for chunk in &node.chunks {
                    //debug!("cas: chunk {}", chunk);
                    let old_id = blob_infos[chunk.inner.blob_index() as usize].blob_id();
                    let chunk_id = chunk.inner.id();
                    /*
                       1. same blob
                       2. different blob, same chunk
                       3. new chunk
                       case 3 will cause download
                    */
                    let chunk_w_o = match cache_chunks.get(chunk_id) {
                        Some(c) => c.clone(),
                        None => {
                            let (new_id, cis) = self.db.add_chunk(&chunk.inner, old_id, 0);
                            if new_id != *old_id {
                                let blob_idx = match new_blobs.get(&new_id) {
                                    Some(i) => i.to_owned(),
                                    None => {
                                        curr_blob_idx += 1;
                                        //just alloc idx here, dump when all chunk check done
                                        new_blobs.insert(new_id.clone(), curr_blob_idx);
                                        curr_blob_idx
                                    }
                                };
                                let mut chunk_w =
                                    serde_json::from_str::<ChunkWrapper>(&cis.unwrap()).unwrap();
                                chunk_w.set_blob_index(blob_idx as u32);
                                cache_chunks.insert(*chunk_w.id(), Some(chunk_w.clone()));
                                Some(chunk_w)
                            } else {
                                cache_chunks.insert(*chunk_id, None);
                                None
                            }
                        }
                    };

                    if let Some(chunk_w) = chunk_w_o {
                        let mut v6_chunk = RafsV6InodeChunkAddr::new();
                        // for erofs, bump id by 1 since device id 0 is bootstrap.
                        v6_chunk.set_blob_index((chunk_w.blob_index() + 1) as u8);
                        v6_chunk.set_blob_comp_index(chunk_w.index());
                        v6_chunk.set_block_addr(
                            (chunk_w.uncompressed_offset() / EROFS_BLOCK_SIZE) as u32,
                        );
                        let mut chunks: Vec<u8> = Vec::new();
                        chunks.extend(v6_chunk.as_ref());

                        writer
                            .seek(SeekFrom::Start(chunk_ofs))
                            .context("failed seek for chunk_ofs")
                            .unwrap();
                        writer
                            .write(chunks.as_slice())
                            .context("failed to write chunkindexes")
                            .unwrap();
                    }

                    chunk_ofs += unit;
                }
                true
            })?;

            debug!(
                "cas: rebuild bootstrap select {:?} {:?}/{:?} ms",
                self.db.select_ops,
                self.db.select_time / self.db.select_ops as u128,
                self.db.select_time / 1000
            );

            let ofs = sb.meta.chunk_table_offset;
            let size = sb.meta.chunk_table_size as usize;
            if size == 0 {
                return Ok(());
            }

            let unit_size = size_of::<RafsV5ChunkInfo>();
            if size % unit_size != 0 {
                panic!("load_chunk_table: invalid rafs v6 chunk table size");
            }

            let chunk_cnt = size / unit_size;
            let mut rw_chunk_cnt = 1;
            let mut rw_uncompressed_size_cnt = 0;
            let mut rw_compressed_size_cnt = 0;

            for chunk_idx in 0..chunk_cnt {
                let cki = sb.superblock.get_chunk_info(chunk_idx)?;
                let mut chunk = ChunkWrapper::from_chunk_info(cki.as_ref());

                if let Some(Some(c)) = cache_chunks.get(chunk.id()) {
                    let chunk_ofs = ofs + (unit_size * chunk_idx) as u64;
                    chunk.copy_from(c);
                    rw_uncompressed_size_cnt += c.uncompressed_size();
                    rw_compressed_size_cnt += c.compressed_size();
                    rw_chunk_cnt += 1;

                    writer
                        .seek_offset(chunk_ofs)
                        .context("failed seek chunk offset")?;
                    chunk
                        .store(writer.as_mut())
                        .context("failed to dump chunk table")?;
                }
            }
            debug!(
                "cas: rw chunk {}/{} comp size {}/{} uncomp size {}/{}",
                rw_chunk_cnt,
                chunk_cnt,
                rw_compressed_size_cnt / rw_chunk_cnt,
                rw_compressed_size_cnt,
                rw_uncompressed_size_cnt / rw_chunk_cnt,
                rw_uncompressed_size_cnt,
            );

            let mut rw_blob_cnt = 0;
            if !new_blobs.is_empty() {
                let mut new_blobs_vec: Vec<(&String, &usize)> = new_blobs.iter().collect();
                new_blobs_vec.sort_by(|a, b| a.1.cmp(b.1));
                for idx in new_blobs_vec {
                    let blob_info = match self.blobs.get(idx.0) {
                        Some(bi) => bi,
                        None => {
                            let bis = self.db.get_blob(idx.0).unwrap();
                            let bi = serde_json::from_str::<BlobInfo>(&bis).unwrap();
                            self.blobs.insert(bi.blob_id().to_owned(), Arc::new(bi));
                            self.blobs.get(idx.0).unwrap()
                        }
                    };
                    let mut blob = BlobInfo::from(blob_info);
                    blob.set_blob_index(*idx.1 as u32);
                    //debug!("cas: rw blob {:?}", blob);
                    blob_infos.push(Arc::new(blob));
                    rw_blob_cnt += 1;
                }
                debug!("cas: new blobs {}", rw_blob_cnt);
                let blob_table = RafsV6BlobTable::from(blob_infos);
                //per devslot 128, per blob 256，check curr size
                //TODO: check blobtable/devtable exist
                let mut sb_v6 = RafsV6SuperBlock::new();
                sb_v6.load(&mut reader)?;
                let mut ext_sb = RafsV6SuperBlockExt::new();
                ext_sb.load(&mut reader)?;

                let ori_devtable_ofs =
                    sb_v6.s_devt_slotoff as u64 * size_of::<RafsV6Device>() as u64;
                let ori_devtable_len = sb.meta.blob_table_offset - ori_devtable_ofs;
                let ori_blob_table_size = sb.meta.blob_table_size as u64;

                // get devt_slotoff
                let mut devtable: Vec<RafsV6Device> = Vec::new();
                for entry in blob_table.entries.iter() {
                    let mut devslot = RafsV6Device::new();
                    // blob id is String, which is processed by sha256.finalize().
                    if entry.blob_id().len() != 64 {
                        panic!(
                            "only blob id of length 64 is supported, blob id {:?}",
                            entry.blob_id()
                        );
                    }
                    devslot.set_blob_id(entry.blob_id().as_bytes()[0..64].try_into().unwrap());
                    devslot.set_blocks(entry.uncompressed_size());
                    devslot.set_mapped_blkaddr(0);
                    devtable.push(devslot);
                }

                let devtable_len = devtable.len() * size_of::<RafsV6Device>();
                let blob_table_size = blob_table.size() as u64;

                //TODO: consider prefetch table
                let (devtable_ofs, blob_table_offset) = if devtable_len as u64
                    > ori_devtable_len + ori_blob_table_size
                {
                    let devtable_ofs = writer
                        .seek_to_end()
                        .context("failed to seek to bootstrap's end for devtable")?;
                    let blob_table_offset =
                        align_offset(devtable_ofs + devtable_len as u64, EROFS_BLOCK_SIZE as u64);
                    (devtable_ofs, blob_table_offset)
                } else {
                    let blob_table_offset = writer
                        .seek_to_end()
                        .context("failed to seek to bootstrap's end for blob table")?;
                    (ori_devtable_ofs, blob_table_offset)
                };

                writer.seek(SeekFrom::Start(0))?;
                sb_v6.set_devt_slotoff(devtable_ofs);
                sb_v6.store(writer.as_mut()).context("failed to store SB")?;
                ext_sb.set_blob_table_offset(blob_table_offset);
                ext_sb.set_blob_table_size(blob_table_size as u32);
                ext_sb
                    .store(writer.as_mut())
                    .context("failed to store extended SB")?;

                // Dump table
                writer
                    .seek_offset(devtable_ofs)
                    .context("failed to seek devtslot")?;
                for slot in devtable.iter() {
                    slot.store(writer.as_mut())
                        .context("failed to store device slot")?;
                }
                writer
                    .seek_offset(blob_table_offset)
                    .context("failed seek for extended blob table offset")?;
                blob_table
                    .store(writer.as_mut())
                    .context("failed to store extended blob table")?;

                /* end */
                let pos = writer
                    .seek_to_end()
                    .context("failed to seek to bootstrap's end")?;
                let padding = align_offset(pos, EROFS_BLOCK_SIZE as u64) - pos;
                let padding_data: [u8; 4096] = [0u8; 4096];
                writer
                    .write_all(&padding_data[0..padding as usize])
                    .context("failed to write 0 to padding of bootstrap's end")?;
                writer.flush().context("failed to flush bootstrap")?;
            }
        } else {
            unimplemented!()
        }

        self.db.flush();

        Ok(())
    }

    fn add_bootstrap(&mut self, file: impl AsRef<Path>, mnt: impl AsRef<Path>) -> PathBuf {
        let start = Instant::now();
        let src = file.as_ref();
        let mnt = mnt.as_ref();
        let mut hasher = DefaultHasher::new();
        src.hash(&mut hasher);
        let cache = PathBuf::from(mnt);

        let obj = match self.path_map.get(src) {
            Some(o) => {
                o.ref_count.fetch_add(1, Ordering::AcqRel);
                o.clone()
            }
            None => {
                let o = Arc::new(BootstrapObject {
                    source: PathBuf::from(src),
                    cache: cache.clone(),
                    ref_count: AtomicU32::new(1),
                });
                self.rebuild_bootstrap(o.clone()).unwrap();
                self.path_map.insert(src.to_owned(), o.clone());
                o
            }
        };
        self.mnt_map.insert(mnt.to_owned(), obj);

        debug!(
            "cas: add bootstrap time cost {:?} ms",
            start.elapsed().as_micros() / 1000
        );
        cache
    }

    fn remove_bootstrap(&mut self, mnt: impl AsRef<Path>) {
        let obj = self.mnt_map.get(mnt.as_ref()).unwrap();
        if obj.ref_count.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.path_map.remove(&obj.source);
        }
        self.mnt_map.remove(mnt.as_ref());
        //TODO: rm bootstrap
    }
}

#[allow(dead_code)]
struct CasDbMgr {
    file: PathBuf,
    conn: Connection,
    select_time: u128,
    select_ops: u64,
    chunk_datas: Vec<TxChunkData>,
}

#[derive(Debug, Clone)]
struct TxChunkData {
    chunk_inner: ChunkWrapper,
    blob_id: String,
    state: u32,
}

impl CasDbMgr {
    fn new(dirpath: impl AsRef<Path>) -> Result<Self, Box<dyn Error>> {
        let file = PathBuf::from(format!(
            "{}/{}",
            dirpath.as_ref().to_str().unwrap(),
            String::from("cas.db")
        ));
        let conn = Connection::open(file.clone())?;
        //let conn = Connection::open_in_memory()?;

        conn.execute(
            "CREATE TABLE IF NOT EXISTS BlobInfos (
            BlobId     TEXT NOT NULL PRIMARY KEY,
            BlobInfo   TEXT NOT NULL
        )",
            (),
        )?;
        conn.execute(
            "CREATE INDEX IF NOT EXISTS BlobIndex ON BlobInfos (BlobId)",
            (),
        )?;

        conn.execute(
            "CREATE TABLE IF NOT EXISTS ChunkState (
            ChunkId           INTEGER PRIMARY KEY,
            ChunkDigestValue  TEXT NOT NULL,
            ChunkInfo         TEXT NOT NULL,
            ChunkState        INTEGER NOT NULL,
            BlobId            TEXT NOT NULL,
            FOREIGN KEY(BlobId) REFERENCES BlobInfos(BlobId)
        )",
            (),
        )?;
        conn.execute(
            "CREATE INDEX IF NOT EXISTS ChunkIndex ON ChunkState (ChunkDigestValue)",
            (),
        )?;

        conn.execute(
            "CREATE TABLE IF NOT EXISTS ChunkReference (
            id       INTEGER PRIMARY KEY,
            BlobId   TEXT NOT NULL,
            ChunkId  INTEGER NOT NULL UNIQUE,
            FOREIGN KEY(BlobId) REFERENCES BlobInfos(BlobId),
            FOREIGN KEY(ChunkId) REFERENCES ChunkState(ChunkId)
        )",
            (),
        )?;

        Ok(CasDbMgr {
            //todo: pre db file
            file,
            conn,
            select_time: 0,
            select_ops: 0,
            chunk_datas: vec![],
        })
    }

    fn add_blob(&self, id: &str, blob_info: &str) -> String {
        if let Ok(blob_id) = self.conn.query_row(
            "SELECT BlobId FROM BlobInfos WHERE BlobId = ?",
            [id],
            |row| row.get::<usize, String>(0),
        ) {
            return blob_id;
        };

        self.conn
            .execute(
                "INSERT INTO BlobInfos (BlobId, BlobInfo)
                VALUES (?1, ?2)",
                (id, blob_info),
            )
            .unwrap();

        id.to_string()
    }

    fn get_blob(&self, id: &str) -> Option<String> {
        if let Ok(blob_info) = self.conn.query_row(
            "SELECT BlobInfo FROM BlobInfos WHERE BlobId = ?",
            [id],
            |row| row.get::<usize, String>(0),
        ) {
            return Some(blob_info);
        };

        None
    }

    fn add_chunk(
        &mut self,
        chunk_inner: &ChunkWrapper,
        blob_id: &str,
        state: u32,
    ) -> (String, Option<String>) {
        //let chunk_info = serde_json::to_string(&chunk_inner).unwrap();
        let chunk_id = chunk_inner.id();

        let db_start = Instant::now();
        if let Ok((id, info)) = self.conn.query_row(
            "SELECT BlobId, ChunkInfo FROM ChunkState INDEXED BY ChunkIndex WHERE ChunkDigestValue = ?",
            [chunk_id.as_ref()],
            |row| Ok((row.get(0)?, row.get(1)?)),
        ) {
            self.select_time += db_start.elapsed().as_micros();
            self.select_ops += 1;
            return (id, info);
        };
        self.select_time += db_start.elapsed().as_micros();
        self.select_ops += 1;

        let td = TxChunkData {
            chunk_inner: chunk_inner.clone(),
            blob_id: String::from(blob_id),
            state,
        };
        self.chunk_datas.push(td);

        (String::from(blob_id), None)
    }

    fn insert_chunk(
        tx: &Transaction,
        chunk_id: &RafsDigest,
        chunk_info: &str,
        blob_id: &str,
        state: u32,
    ) {
        tx.execute(
            "INSERT INTO ChunkState (ChunkDigestValue, ChunkInfo, ChunkState, BlobId)
                VALUES (?1, ?2, ?3, ?4)",
            (chunk_id.as_ref(), chunk_info, state, blob_id),
        )
        .unwrap();

        let id = tx
            .query_row(
                "SELECT ChunkId FROM ChunkState WHERE ChunkDigestValue = ?1 AND BlobId = ?2",
                (chunk_id.as_ref(), blob_id),
                |row| row.get::<usize, u64>(0),
            )
            .unwrap();
        tx.execute(
            "INSERT INTO ChunkReference (ChunkId, BlobId)
                VALUES (?1, ?2)",
            (&id, blob_id),
        )
        .unwrap();
    }

    fn flush(&mut self) {
        let mut insert_time: u128 = 0;
        let mut insert_ops: u64 = 1;
        let mut insert_comp_size_cnt = 0;
        let mut insert_uncomp_size_cnt = 0;
        let db_start = Instant::now();
        let tran = self.conn.transaction().unwrap();
        for data in &self.chunk_datas {
            let chunk_info = serde_json::to_string(&data.chunk_inner).unwrap();
            let chunk_id = data.chunk_inner.id();
            CasDbMgr::insert_chunk(&tran, chunk_id, &chunk_info, &data.blob_id, data.state);
            insert_ops += 1;
            insert_comp_size_cnt += data.chunk_inner.compressed_size();
            insert_uncomp_size_cnt += data.chunk_inner.uncompressed_size();
        }
        insert_time += db_start.elapsed().as_micros();
        tran.commit().unwrap();
        debug!(
            "cas: rebuild bootstrap insert {:?} {:?}/{:?} ms {} {}",
            insert_ops,
            insert_time / insert_ops as u128,
            insert_time / 1000,
            insert_comp_size_cnt,
            insert_uncomp_size_cnt,
        );
    }

    fn _set_chunk_state_range(&self, _blob_id: &str, _start: u64, _size: u64) {
        todo!()
    }

    fn _delete_chunks(&self, _blob_id: Option<&str>, _chunk_id: Option<&str>) -> u64 {
        todo!()
    }
}
