/** @file
  Disk utilities

  Copyright (c) 2021 - 2023 Pedro Falcato All rights reserved.
  SPDX-License-Identifier: BSD-2-Clause-Patent
**/
#include "Ext4Dxe.h"
#include <Library/TimerLib.h>

/**
  Compare two EXT4_BUFFER structs.
  Used in the block cache's ORDERED_COLLECTION.

  @param[in] UserStruct1  Pointer to the first user structure.

  @param[in] UserStruct2  Pointer to the second user structure.

  @retval <0  If UserStruct1 compares less than UserStruct2.

  @retval  0  If UserStruct1 compares equal to UserStruct2.

  @retval >0  If UserStruct1 compares greater than UserStruct2.
**/
STATIC
INTN
EFIAPI
Ext4BlockCacheStructCompare (
  IN CONST VOID  *UserStruct1,
  IN CONST VOID  *UserStruct2
  )
{
  CONST EXT4_BUFFER  *Buf1;
  CONST EXT4_BUFFER  *Buf2;

  Buf1 = UserStruct1;
  Buf2 = UserStruct2;

  return Buf1->BlockNr < Buf2->BlockNr ? -1 :
         Buf1->BlockNr > Buf2->BlockNr ? 1 : 0;
}

/**
  Compare a standalone key against a EXT4_BUFFER containing an embedded key.
  Used in the block cache's ORDERED_COLLECTION.

  @param[in] StandaloneKey  Pointer to the bare key.

  @param[in] UserStruct     Pointer to the user structure with the embedded
                            key.

  @retval <0  If StandaloneKey compares less than UserStruct's key.

  @retval  0  If StandaloneKey compares equal to UserStruct's key.

  @retval >0  If StandaloneKey compares greater than UserStruct's key.
**/
STATIC
INTN
EFIAPI
Ext4BlockCacheKeyCompare (
  IN CONST VOID  *StandaloneKey,
  IN CONST VOID  *UserStruct
  )
{
  CONST EXT4_BUFFER  *Buffer;
  EXT4_BLOCK_NR      Block;

  Buffer = UserStruct;
  Block  = (UINTN)StandaloneKey;

  return Block < Buffer->BlockNr ? -1 :
         Block > Buffer->BlockNr ? 1 : 0;
}

/**
   Initialises the (empty) LRU block cache

   @param[in]      Partition        Pointer to the open partition.

   @return Result of the operation.
**/
EFI_STATUS
Ext4InitBlockCache (
  IN EXT4_PARTITION  *Partition
  )
{
  Partition->BlockCache.BlockCache = OrderedCollectionInit (Ext4BlockCacheStructCompare, Ext4BlockCacheKeyCompare);
  if (Partition->BlockCache.BlockCache == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  Partition->BlockCache.NrCachedBlocks = Partition->BlockCache.NrLruBlocks = 0;
  InitializeListHead (&Partition->BlockCache.LruList);

  return EFI_SUCCESS;
}

VOID
Ext4GetBuffer (
  EXT4_BUFFER  *Buffer
  )
{
  ASSERT (Buffer->Refcount < MAX_UINT32);
  Buffer->Refcount++;
}

VOID
Ext4PutBuffer (
  EXT4_PARTITION  *Partition,
  EXT4_BUFFER     *Buffer
  )
{
  ASSERT (Buffer->Refcount > 0);
  if (--Buffer->Refcount == 0) {
    // Put this buffer on the tail of the LRU list
    InsertTailList (&Partition->BlockCache.LruList, &Buffer->LruList);
    Partition->BlockCache.NrLruBlocks++;
  }
}

STATIC
EFI_STATUS
Ext4CreateBuffer (
  IN EXT4_PARTITION  *Partition,
  IN EXT4_BLOCK_NR   BlockNr,
  OUT EXT4_BUFFER    **Buffer
  )
{
  EXT4_BUFFER      *Buf;
  EXT4_BLOCKCACHE  *Bcache;
  EFI_STATUS       Status;

  Bcache  = &Partition->BlockCache;
  *Buffer = NULL;

  if ((Bcache->NrCachedBlocks >= EXT4_BLOCK_CACHE_SIZE) && (Bcache->NrLruBlocks > 0)) {
    // If we're over the limit, reuse the least recently used buffer
    // by popping the head of the list.
    Buf = BASE_CR (GetFirstNode (&Bcache->LruList), EXT4_BUFFER, LruList);
    ASSERT (Buf->Refcount == 0);

    RemoveEntryList (&Buf->LruList);
    Bcache->NrLruBlocks--;
    Buf->BlockNr = BlockNr;
  } else {
    Buf = AllocateZeroPool (sizeof (EXT4_BUFFER));
    if (Buf == NULL) {
      return EFI_OUT_OF_RESOURCES;
    }

    Buf->Buffer = AllocatePool (Partition->BlockSize);
    if (Buf->Buffer == NULL) {
      FreePool (Buf);
      return EFI_OUT_OF_RESOURCES;
    }

    Buf->BlockNr = BlockNr;
    Bcache->NrCachedBlocks++;
  }

  Status = Ext4ReadBlocks (Partition, Buf->Buffer, 1, Buf->BlockNr);

  if (EFI_ERROR (Status)) {
    goto OutDestroyBuf;
  }

  Status = OrderedCollectionInsert (Partition->BlockCache.BlockCache, NULL, Buf);
  if (Status != EFI_SUCCESS) {
    goto OutDestroyBuf;
  }

  *Buffer = Buf;
  Ext4GetBuffer (Buf);

  DEBUG ((DEBUG_INFO, "[ext4] Created buffer for block %lu in the cache (size now %u)\n", BlockNr, Bcache->NrCachedBlocks));

  return Status;
OutDestroyBuf:
  FreePool (Buf->Buffer);
  FreePool (Buf);
  Bcache->NrCachedBlocks--;
  return Status;
}

EFI_STATUS
Ext4FindBuffer (
  IN EXT4_PARTITION  *Partition,
  IN EXT4_BLOCK_NR   BlockNr,
  OUT EXT4_BUFFER    **Buffer
  )
{
  ORDERED_COLLECTION_ENTRY  *Entry;
  EXT4_BUFFER               *Buf;
  EFI_STATUS                Status;

  Status = EFI_SUCCESS;
  Buf    = NULL;
  Entry  = OrderedCollectionFind (Partition->BlockCache.BlockCache, (CONST VOID *)BlockNr);

  if (Entry != NULL) {
    // Buffer cache hit!
    Buf = OrderedCollectionUserStruct (Entry);

    if (Buf->Refcount == 0) {
      // Unlink from LRU
      RemoveEntryList (&Buf->LruList);
      Partition->BlockCache.NrLruBlocks--;
    }

    Ext4GetBuffer (Buf);
    DEBUG ((DEBUG_INFO, "[ext4] Found Block %lu in the cache\n", BlockNr));
    goto Out;
  }

  Status = Ext4CreateBuffer (Partition, BlockNr, &Buf);

Out:
  *Buffer = Buf;
  return Status;
}

/**
   Reads from the partition's disk using the DISK_IO protocol.

   @param[in]  Partition      Pointer to the opened ext4 partition.
   @param[out] Buffer         Pointer to a destination buffer.
   @param[in]  Length         Length of the destination buffer.
   @param[in]  Offset         Offset, in bytes, of the location to read.

   @return Success status of the disk read.
**/
EFI_STATUS
Ext4ReadDiskIo (
  IN EXT4_PARTITION  *Partition,
  OUT VOID           *Buffer,
  IN UINTN           Length,
  IN UINT64          Offset
  )
{
  UINT64  Start, End;

  if (Partition->BlockSize != 0) {
    DEBUG ((DEBUG_INFO, "[ext4] Reading block %lu\n", Offset / Partition->BlockSize));
  }

  Start = GetPerformanceCounter ();

  EFI_STATUS  st = EXT4_DISK_IO (Partition)->ReadDisk (
                                               EXT4_DISK_IO (Partition),
                                               EXT4_MEDIA_ID (Partition),
                                               Offset,
                                               Length,
                                               Buffer
                                               );

  End = GetPerformanceCounter ();
  DEBUG ((DEBUG_INFO, "[ext4] request took %luuS\n", GetTimeInNanoSecond (End - Start) / 1000));
  return st;
}

/**
   Reads blocks from the partition's disk using the DISK_IO protocol.

   @param[in]  Partition      Pointer to the opened ext4 partition.
   @param[out] Buffer         Pointer to a destination buffer.
   @param[in]  NumberBlocks   Length of the read, in filesystem blocks.
   @param[in]  BlockNumber    Starting block number.

   @return Success status of the read.
**/
EFI_STATUS
Ext4ReadBlocks (
  IN EXT4_PARTITION  *Partition,
  OUT VOID           *Buffer,
  IN UINTN           NumberBlocks,
  IN EXT4_BLOCK_NR   BlockNumber
  )
{
  UINT64  Offset;
  UINTN   Length;

  ASSERT (NumberBlocks != 0);
  ASSERT (BlockNumber != EXT4_BLOCK_FILE_HOLE);

  Offset = MultU64x32 (BlockNumber, Partition->BlockSize);
  Length = NumberBlocks * Partition->BlockSize;

  // Check for overflow on the block -> byte conversions.
  // Partition->BlockSize is never 0, so we don't need to check for that.

  if (DivU64x64Remainder (Offset, BlockNumber, NULL) != Partition->BlockSize) {
    return EFI_INVALID_PARAMETER;
  }

  if (Length / NumberBlocks != Partition->BlockSize) {
    return EFI_INVALID_PARAMETER;
  }

  return Ext4ReadDiskIo (Partition, Buffer, Length, Offset);
}

/**
   Allocates a buffer and reads blocks from the partition's disk using the DISK_IO protocol.
   This function is deprecated and will be removed in the future.

   @param[in]  Partition      Pointer to the opened ext4 partition.
   @param[in]  NumberBlocks   Length of the read, in filesystem blocks.
   @param[in]  BlockNumber    Starting block number.

   @return Buffer allocated by AllocatePool, or NULL if some part of the process
           failed.
**/
VOID *
Ext4AllocAndReadBlocks (
  IN EXT4_PARTITION  *Partition,
  IN UINTN           NumberBlocks,
  IN EXT4_BLOCK_NR   BlockNumber
  )
{
  VOID   *Buf;
  UINTN  Length;

  // Check that number of blocks isn't empty, because
  // this is incorrect condition for opened partition,
  // so we just early-exit
  if ((NumberBlocks == 0) || (BlockNumber == EXT4_BLOCK_FILE_HOLE)) {
    return NULL;
  }

  Length = NumberBlocks * Partition->BlockSize;

  // Check for integer overflow
  if (Length / NumberBlocks != Partition->BlockSize) {
    return NULL;
  }

  Buf = AllocatePool (Length);
  if (Buf == NULL) {
    return NULL;
  }

  if (Ext4ReadBlocks (Partition, Buf, NumberBlocks, BlockNumber) != EFI_SUCCESS) {
    FreePool (Buf);
    return NULL;
  }

  return Buf;
}
