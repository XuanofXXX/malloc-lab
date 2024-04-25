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
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    "shi ra na i",
    "Xia Chunxuan",
    "xiachunxuan@ruc.edu.cn",
    "",
    ""
};

#define DEBUG
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define FSIZE 16
#define CHUNKSIZE ((1<<12) + (1<<5)) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
// #define GET_8B(p) (*(void **)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define PUT_8B(p, val) (*(void **)p = (unsigned long)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p) (GET(p) & 0b10)
#define SET_ALLOC(p)        (GET(p) |= 0x1)
#define SET_FREE(p)         (GET(p) &= ~0x1)
#define SET_PREV_ALLOC(p)   (GET(p) |= 0x2)
#define SET_PREV_FREE(p) (GET(p) &= ~0b10)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Segregate list*/
#define NEXT_FREE(bp) ((void **)(bp))
#define PREV_FREE(bp) ((void **)(bp) + 1)
#define GET_NEXT(bp) (*(NEXT_FREE(bp)))
#define GET_PREV(bp) (*(PREV_FREE(bp)))
#define SET_NEXT(bp, val) (GET_NEXT(bp) = (unsigned long)(val))
#define SET_PREV(bp, val) (GET_PREV(bp) = (unsigned long)(val))


static void *extend_heap(size_t words);
// static void *best_fit(size_t asize);
// static void *next_fit(size_t asize);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static size_t get_index(size_t size);
static void insert_block(void *bp);
static void delete_block(void *bp);

#ifdef DEBUG
static void show_block(void *bp);
#endif

static char *heap_listp;
static char *pre_listp;
// static void **segregate_list;
static char *base_listp;

static size_t get_index(size_t size){
    if (size <= 0)
        return NULL;
    if (0 < size && size <= 16) return 0;
    if (16 < size && size <= 32) return 1;
    if (32 < size && size <= 64) return 2;
    if (64 < size && size <= 128) return 3;
    if (128 < size && size <= 256) return 4;
    if (256 < size && size <= 512) return 5;
    if (512 < size && size <= 1024) return 6;
    if (1024 < size && size <= 2048) return 7;
    if (2048 < size && size <= 4096) return 8;
    if (4096 < size && size <= 8192) return 9;
    if (8192 < size && size <= 16384) return 10;
    if (16384 < size && size <= 32768) return 11;
    if (32768 < size && size <= 65536) return 12;
    if (65536 < size && size <= 131072) return 13;
    if (131072 < size && size <= 262144) return 14;
    if (262144 < size && size <= 524288) return 15;
    if (524288 < size && size <= 1048576) return 16;
    if (1048576 < size && size <= 2097152) return 17;
    if (2097152 < size && size <= 4194304) return 18;
    return NULL;
}

static void insert_block(void *bp){
    #ifdef DEBUG
        printf("inserting blocks...\n");
        // show_block(bp);
    #endif
    size_t size = GET_SIZE(HDRP(bp)) - WSIZE;
    size_t index = get_index(size);

    void *head = base_listp + index * DSIZE;
    void *head_node = GET_NEXT(head);
    void *cur = head_node;

    if (head_node == NULL){
        SET_NEXT(head, bp);
        SET_NEXT(bp, NULL);
        SET_PREV(bp, NULL);
    }else{
        void* next = GET_NEXT(head_node);
        SET_NEXT(head, bp);
        SET_NEXT(bp, next);
        SET_PREV(bp, head);
        SET_PREV(next, bp);
    }
}

static void delete_block(void *bp){
    /*
    * 不会改变bp块的状态，包括是否分配等等
    */
    #ifdef DEBUG
    printf("deleting blocks...\n");
    // show_block(bp);
    #endif
    size_t size = GET_SIZE(HDRP(bp)) - WSIZE;
    size_t index = get_index(size);

    void *prev = GET_PREV(bp);
    void *next = GET_NEXT(bp);
    void *head = base_listp + index*DSIZE;
    void *head_node = GET_NEXT(head);

    if (head_node == bp){
        SET_NEXT(head, next);
    }else{
        // SET_NEXT(bp, NULL);
        // SET_PREV(bp, NULL);
        if (prev != NULL) SET_NEXT(prev, next);
        if (next != NULL) SET_PREV(next, prev);
    }

}

static void *find_fit(size_t asize){
    #ifdef DEBUG
        printf("finding fitable block...\n");
    #endif
    size_t size = asize - WSIZE;
    size_t index = get_index(size);

    void *cur = base_listp + index* DSIZE;
    void *bp = NULL;
    size_t minsize = __INT32_MAX__;
    while (GET_NEXT(cur) != NULL)
    {
        if (GET_SIZE(HDRP(cur)) <= minsize){
            minsize = GET_SIZE(HDRP(cur));
            bp = cur;
        }
        cur = GET_NEXT(cur);
    }
    return bp;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    #ifdef DEBUG
        printf("init mm...\n");
    #endif
    int initsize = 19 * DSIZE + 4 * WSIZE;
    /* Create the initial empty heap */
    if ((base_listp = mem_sbrk(initsize)) == (void *)-1)
        return -1;
    
    memset(base_listp, 0, initsize);

    heap_listp = base_listp + 19 * DSIZE;
    
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 0b11)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 0b11)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 0b11)); /* Epilogue header */

    heap_listp += (2*WSIZE);
    pre_listp = heap_listp;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    #ifdef DEBUG
        printf("extending beap...\n");
    #endif
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */

    size = MAX(
            ((words % 2) ? (words+1) * WSIZE : words * WSIZE), 
            2 * WSIZE + 2 * DSIZE
            );
    
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    size_t prev_alloced = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACK(size, prev_alloced | 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, prev_alloced | 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0b11)); /* New epilogue header */
    // insert_block(bp);

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void place(void *bp, size_t asize)
{
    // size_t size = GET_SIZE(HDRP(bp));
    
    // if ((size - asize) >= (3 * DSIZE)) {
    //     PUT(HDRP(bp),PACK(asize,1));
    //     PUT(FTRP(bp),PACK(asize,1));
    //     PUT(HDRP(NEXT_BLKP(bp)),PACK(size - asize,0));
    //     PUT(FTRP(NEXT_BLKP(bp)),PACK(size - asize,0));
    // } else {
    //     PUT(HDRP(bp),PACK(size,1));
    //     PUT(FTRP(bp),PACK(size,1));
    // }
    // pre_listp = bp;
    #ifdef DEBUG
        printf("placing...\n");
    #endif
    size_t cur_size = GET_SIZE(HDRP(bp));
    size_t remain_size = cur_size - asize;
    delete_block(bp);
    // 如果剩余块大小小于最小块大小，则不分割
    if (remain_size < 2 * DSIZE) {
        // 不改变块大小，只改变分配标志位，从而规避产生不可回收的外部碎片
        SET_ALLOC(HDRP(bp));

        // 如果下一个块是分配块，则只设置其头部
        SET_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
        // 如果下一个块是空闲块，则还需要设置其脚部
        if (!GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {
            SET_PREV_ALLOC(FTRP(NEXT_BLKP(bp)));
        }
    }
    // 如果剩余块大小大于等于最小块大小，则分割，下一个块必为空闲块
    else {
        // 设置当前块头部
        PUT(HDRP(bp), PACK(asize, GET_PREV_ALLOC(HDRP(bp)) | 1));
        // 设置剩余块的头部和脚部
        // 次低位（上一个块为分配块）设置为1，最低位（当前块为分配块）设置为0
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remain_size, 0b10));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remain_size, 0b10));
        // 将下一个块插入空闲链表
        insert_block(NEXT_BLKP(bp));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    #ifdef DEBUG
        printf("freeing...\n");
    #endif
    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACK(size, prev_alloc | 0));
    PUT(FTRP(bp), PACK(size, prev_alloc | 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    #ifdef DEBUG
        // printf("coalescing...\n");
    #endif
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { // Case 1 
    #ifdef DEBUG
        printf("coalescing case 1...\n");
        #endif
        pre_listp = bp;
        SET_PREV_FREE(HDRP(NEXT_BLKP(bp)));
    }
    else if (prev_alloc && !next_alloc) { /* Case 2 */
    #ifdef DEBUG
        printf("coalescing case 2...\n");
        #endif
        delete_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0b10));
        PUT(FTRP(bp), PACK(size, 0b10));
    }

    else if (!prev_alloc && next_alloc) { /* Case 3 */
        #ifdef DEBUG
        printf("coalescing case 3...\n");
        printf("the info of bp is %p\n", bp);
        printf("prev: %p, size: %d\n", GET_PREV(bp), GET_SIZE(HDRP(GET_PREV(bp))));
        // printf("the info of PREV_BLKP(PREV_BLKP(bp)) is %p\n", PREV_BLKP(PREV_BLKP(bp)));
        // printf("the info of NEXT_BLKP(NEXT_BLKP(bp)) is %p\n", NEXT_BLKP(NEXT_BLKP(bp)));
        #endif 
        delete_block(PREV_BLKP(bp));
        SET_PREV_FREE(HDRP(NEXT_BLKP(bp)));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, prev_prev_alloc | 0));
        PUT(FTRP(bp), PACK(size, prev_prev_alloc | 0));
        bp = PREV_BLKP(bp);
    }

    else { /* Case 4 */
        #ifdef DEBUG
        printf("coalescing case 4...\n");
        #endif
        delete_block(NEXT_BLKP(bp));
        delete_block(PREV_BLKP(bp));

        size += (
            GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)))
            );
        
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, prev_prev_alloc | 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, prev_prev_alloc | 0));
        bp = PREV_BLKP(bp);
    }
    pre_listp = bp;
    insert_block(bp);
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    #ifdef DEBUG
        printf("mallocing blocks...\n");
    #endif
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else // 只需要存header，不需要存footer
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE);

    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }else{
        extend_heap(CHUNKSIZE/WSIZE);
        if ((bp = find_fit(asize)) != NULL) {
            place(bp, asize);
            return bp;
        }
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void *mm_realloc(void *ptr, size_t size){
    #ifdef DEBUG
        printf("reallocing blocks...\n");
    #endif
    size_t oldsize;
    void* newptr;
    // size 为 0，相当于 free
    if (size == 0) {
        free(ptr);
        return 0;
    }
    // ptr 为 NULL，相当于 malloc
    if (ptr == NULL) {
        return malloc(size);
    }
    newptr = malloc(size);
    // realloc() 失败，原块保持不变
    if (!newptr) {
        return 0;
    }
    // 拷贝原有数据，但是可能会产生截断
    oldsize = GET_SIZE(HDRP(ptr));
    oldsize = MIN(oldsize, size);
    memcpy(newptr, ptr, oldsize);
    // 释放原有块
    free(ptr);
    return newptr;
}
/*
void *_mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
       return mm_malloc(size);
    if (size == 0) {
       mm_free(ptr);
       return NULL;
    }
    size_t adjust_size = ALIGN(size);
    size_t adjust_asize = adjust_size + DSIZE;
    size_t old_size = GET_SIZE(HDRP(ptr));
    if(adjust_size < old_size)
    {
        return ptr;
    }
    if(!GET_ALLOC(NEXT_BLKP(ptr)))
    {
        void *next = NEXT_BLKP(ptr);
        size_t next_size = GET_SIZE(HDRP(next));
        size_t total_asize = old_size + next_size;
        if(total_asize > adjust_asize)
        {
            void * new_next = (char *)ptr + adjust_asize;
            PUT(HDRP(ptr),PACK(adjust_asize,1));
            PUT(FTRP(ptr),PACK(adjust_asize,1));
            PUT(HDRP(new_next), PACK(total_asize - adjust_asize, 0));
            PUT(FTRP(new_next), PACK(total_asize - adjust_asize, 0));
            if(next == pre_listp)
            {
                pre_listp = ptr;
            }
            return ptr;
        }
    }
    // else if(!GET_ALLOC(PREV_BLKP(ptr)))
    // {
    //     void *prev = PREV_BLKP(ptr);
    //     size_t pre_size = GET_SIZE(HDRP(prev));
    //     size_t size = old_size + pre_size + WSIZE;
    //     if(adjust_size <= size)
    //     {
    //         PUT(HDRP(prev), PACK(size, 0));
    //         PUT(FTRP(ptr), PACK(size, 0));
    //         if(ptr == pre_listp)
    //         {
    //             pre_listp = prev;
    //         }
    //         place(prev, adjust_size);
    //         return prev;
    //     }
    // }
    void *newptr;
    size_t copySize;
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    size = GET_SIZE(HDRP(ptr));
    copySize = GET_SIZE(HDRP(newptr));
    if (size < copySize)
      copySize = size;
    memmove(newptr, ptr, copySize - WSIZE);
    mm_free(ptr);
    return newptr;
}
*/

// static void *best_fit(size_t size){
//     void *ptr = heap_listp;
//     void *min = NULL;
//     int residual = __INT32_MAX__;
//     while(GET_SIZE(HDRP(ptr)) > 0)
//     {
//         if ((!GET_ALLOC(HDRP(ptr))) && (GET_SIZE(HDRP(ptr)) >= size)){ // free block && enough space
//             size_t cur_size = GET_SIZE(HDRP(ptr));
//             if (cur_size - size <= residual){
//                 // TODO <= or <
//                 residual = cur_size - size;
//                 min = ptr;
//             }
//         }
//         ptr = NEXT_BLKP(ptr);
//     }
//     return min;
// }

// static void *next_fit(size_t size) {
//     void *bp;
//     void *min = pre_listp;
//     int extra = 50;
//     for(; GET_SIZE(HDRP(min)) > 0; min = NEXT_BLKP(min)){
//         if (!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min)))) {
//             break;
//         }
//     }
//     int count = 0;
//     for (bp = pre_listp; GET_SIZE(HDRP(bp)) > 0 && count < extra; bp = NEXT_BLKP(bp)) {
//         count++;
//         if (!GET_ALLOC(HDRP(bp)) && (size <= GET_SIZE(HDRP(bp)))) {
//             if(GET_SIZE(HDRP(min)) > GET_SIZE(HDRP(bp)))
//             {
//                 min = bp;
//             }
//         }
//     }

//     bp = min;

//     if(!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min))))
//     {
//         pre_listp = bp;
//         return bp;
//     }

//     for(min = heap_listp; GET_SIZE(HDRP(min)) > 0; min = NEXT_BLKP(min)){
//         if (!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min)))) {
//             break;
//         }
//     }

//     count = 0;

//     for (bp = pre_listp; GET_SIZE(HDRP(bp)) > 0 && count < extra; bp = NEXT_BLKP(bp)) {
//         count++;
//         if (!GET_ALLOC(HDRP(bp)) && (size <= GET_SIZE(HDRP(bp)))) {
//             if(GET_SIZE(HDRP(min)) > GET_SIZE(HDRP(bp)))
//             {
//                 min = bp;
//             }
//         }
//     }

//     bp = min;

//     if(!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min))))
//     {
//         pre_listp = bp;
//         return bp;
//     }
    
//     return NULL; /* No fit */
// }

static void show_block(void *bp){
    printf("==========================================\n");
    printf("bp is %p\n", bp);
    printf("size is %d\n", GET_SIZE(HDRP(bp)));
    printf("alloced? %d\n", GET_ALLOC(HDRP(bp)));
    printf("prev_alloced? %d\n", GET_PREV_ALLOC(HDRP(bp)));
    printf("==========================================\n");
}