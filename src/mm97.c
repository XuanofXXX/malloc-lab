/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "top_arasaka",
    /* First member's full name */
    "David Martinez",
    /* First member's email address */
    "DavidMartinez@arasaka.edu.nc",
    /* Second member's full name (leave blank if none) */
    "XCX",
    /* Second member's email address (leave blank if none) */
    "xiachunxuan@ruc.edu.cn"};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */
#define MINBLOCKSIZE 16

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc)                                                      \
  ((size) | (alloc)) /* Pack a size and allocated bit into a word */

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
/* Read the size and the alloc field field from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
/* Given block ptr bp, compute address of its header and footer*/
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* Given block ptr bp, compute address of next and prev blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE((char *)(bp)-DSIZE))
/* Get and set prev or next pointer from address p */
#define GET_PREV(p) (*(unsigned int *)(p))
#define SET_PREV(p, prev) (*(unsigned int *)(p) = (prev))
#define GET_NEXT(p) (*((unsigned int *)(p) + 1))
#define SET_NEXT(p, val) (*((unsigned int *)(p) + 1) = (val))

static void *find_fit(size_t size, int seg_idx) {
  // First Fit
  char *res;
  while (seg_idx < SEG_LEN) {
    char *root = global_list_start_ptr + seg_idx * WSIZE;
    char *bp = (char *)SUCC_BLKP(root);
    while (bp) {
      if ((size_t)CRT_BLKSZ(bp) >= size)
        return bp;
      bp = (char *)SUCC_BLKP(bp);
    }
    // 在这类中未找到适合，在更大类中寻找
    seg_idx++;
  }
  return NULL;
}

void *mm_realloc(void *ptr, size_t size) {
  // 如果 ptr == NULL 直接分配
  if (ptr == NULL)
    return mm_malloc(size);
  // 如果 size == 0 就释放
  else if (size == 0) {
    mm_free(ptr);
    return NULL;
  }
  size_t asize = align_size(size), old_size = CRT_BLKSZ(ptr);
  size_t mv_size = MIN(asize, old_size);
  char *oldptr = ptr;
  char *newptr;
  if (old_size == asize)
    return ptr;
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
  size_t next_size = NEXT_BLKSZ(ptr);
  char *next_bp = NEXT_BLKP(ptr);
  size_t total_size = old_size;
  if (prev_alloc && !next_alloc && (old_size + next_size >= asize)) {
    // 后空闲
    total_size += next_size;
    delete_free_block(next_bp);
    PUT(HDRP(ptr), PACK(total_size, 1));
    PUT(FTRP(ptr), PACK(total_size, 1));
    place(ptr, total_size);
  } else if (!next_size && asize >= old_size) {
    // 如果后部是结尾块，则直接 extend_heap
    size_t extend_size = asize - old_size;
    if ((long)(mem_sbrk(extend_size)) == -1)
      return NULL;
    PUT(HDRP(ptr), PACK(total_size + extend_size, 1));
    PUT(FTRP(ptr), PACK(total_size + extend_size, 1));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
    place(ptr, asize);
  } else { // 直接分配
    newptr = mm_malloc(asize);
    if (newptr == NULL)
      return NULL;
    memcpy(newptr, ptr, MIN(old_size, size));
    mm_free(ptr);
    return newptr;
  }
  return ptr;
}