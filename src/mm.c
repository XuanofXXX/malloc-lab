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

// #define DEBUG
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
#define NUM_LISTS 19
#define FREE_BLOCK_MIN 24

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
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);
static void *coalesce(void *bp);
static size_t get_index(size_t size);
static void insert_block(void *bp);
static void delete_block(void *bp);
static size_t adjust_alloc_size(size_t size);

#ifdef DEBUG
static void print_heap();
static void show_block(void *bp);
static void show_linklist();
static void _check_heap();
#endif

static char *heap_listp;
static char *pre_listp;
// static void **segregate_list;
static char *base_listp;


static size_t get_index(size_t size){
    if (size <= 0)
        return NULL;
    if (size <= 24) return 0;
    if (size <= 32) return 1;
    if (size <= 64) return 2;
    if (size <= 80) return 3;
    if (size <= 128) return 4;
    if (size <= 256) return 5;
    if (size <= 512) return 6;
    if (size <= 1024) return 7;
    if (size <= 2048) return 8;
    if (size <= 4096) return 9;
    if (size <= 8192) return 10;
    if (size <= 16384) return 11;
    if (size <= 32768) return 12;
    if (size <= 65536) return 13;
    if (size <= 131072) return 14;
    if (size <= 262144) return 15;
    if (size <= 524288) return 16;
    if (size <= 1048576) return 17;
    return 18;
}

static size_t adjust_alloc_size(size_t size){
    // if (110 <= size && size <= 128) return 128;
    // if (220 <= size && size <= 256) return 256;
    // if (440 <= size && size <= 512) return 512;
    // if (880 <= size && size <= 1024) return 1024;
    // if (1920 <= size && size <= 2048) return 2048;
    // if (3900 <= size && size <= 4096) return 4096;

    if (size >= 72 && size <= 80) return 80;
    if (size >= 112 && size < 128) return 128;
    if (size >= 240 && size < 256) return 256;
    if (size >= 448 && size < 512) return 512;
    if (size >= 1000 && size < 1024) return 1024;
    if (size >= 2000 && size < 2048) return 2048;
    if (size >= 4072 && size < 4096) return 4096;
    if (size >= 8100 && size < 8192) return 8192;
    if (size >= 16300 && size < 16384) return 16384;
    return size;
}

static void insert_block(void *bp){
    #ifdef DEBUG
        printf("inserting blocks...\n");
        // show_block(bp);
    #endif
    size_t asize = GET_SIZE(HDRP(bp));
    assert(asize >= FREE_BLOCK_MIN);
    size_t index = get_index(asize);

    void *head = base_listp + index * DSIZE;
    void *head_node = GET_NEXT(head);
    void *cur = head_node;

    if (head_node == NULL){
        // *(void **)head = bp;
        SET_NEXT(head, bp);
        head_node = GET_NEXT(head);
        SET_NEXT(bp, NULL);
        SET_PREV(bp, NULL);
    }else{
        void* next = GET_NEXT(head_node);
        SET_NEXT(head_node, bp);
        SET_NEXT(bp, next);
        SET_PREV(bp, head_node);
        if (next != NULL) SET_PREV(next, bp);
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
    size_t asize = GET_SIZE(HDRP(bp));
    size_t index = get_index(asize);

    void *prev = GET_PREV(bp);
    void *next = GET_NEXT(bp);
    void *head = base_listp + index*DSIZE;
    void *head_node = GET_NEXT(head);

    if (head_node == bp){
        SET_NEXT(head, next);
        if (next != NULL) SET_PREV(next, NULL);
    }else{
        if (prev != NULL) SET_NEXT(prev, next);
        if (next != NULL) SET_PREV(next, prev);
        // SET_NEXT(bp, NULL);
        // SET_PREV(bp, NULL);
    }
}

static void *find_fit(size_t asize){
    #ifdef DEBUG
        printf("finding fitable block...\n");
    #endif
    assert(asize > WSIZE);
    size_t index = get_index(asize);
    void *head = base_listp + index* DSIZE;
    void *cur = GET_NEXT(head);
    void *bp = NULL;
    size_t minsize = __INT32_MAX__;
    while (cur != NULL)
    {
        size_t cur_size = GET_SIZE(HDRP(cur));
        if (cur_size >= asize && cur_size <= minsize){
            minsize = cur_size;
            bp = cur;
        }
        cur = GET_NEXT(cur);
    }
    if (bp == NULL){
        for (size_t i = index + 1; i < NUM_LISTS; i++)
        {
            void *head = base_listp + i*DSIZE;
            void *cur = GET_NEXT(head);
            while (cur != NULL)
            {
                size_t cur_size = GET_SIZE(HDRP(cur));
                if (cur_size >= asize && cur_size <= minsize){
                    minsize = cur_size;
                    bp = cur;
                }
                cur = GET_NEXT(cur);
            }
            if (bp != NULL) return bp;
        }
    }
    return bp;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    #ifdef DEBUG
        printf("************************************************************************\n");
        printf("************************************************************************\n");
        printf("************************************************************************\n");
        printf("***  init mm...\n");
    #endif
    int initsize = NUM_LISTS * DSIZE + 4 * WSIZE;
    /* Create the initial empty heap */
    if ((base_listp = mem_sbrk(initsize)) == (void *)-1)
        return -1;
    
    memset(base_listp, 0, initsize);

    heap_listp = base_listp + NUM_LISTS * DSIZE;
    
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
            FREE_BLOCK_MIN
            );
    
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    assert((void *)bp + size <= (char *)mem_heap_hi() + 1);
    /* Initialize free block header/footer and the epilogue header */
    size_t prev_alloced = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACK(size, prev_alloced | 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, prev_alloced | 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0b01)); /* New epilogue header */
    // SET_PREV_FREE(HDRP(NEXT_BLKP(bp)));

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *place(void *bp, size_t asize)
{

    #ifdef DEBUG
        printf("placing...\n");
        assert(NULL == GET_ALLOC(HDRP(bp)));
        assert(GET_SIZE(HDRP(bp)) >= asize);
    #endif
    void *new_bp = bp;
    size_t free_asize = GET_SIZE(HDRP(bp));
    size_t remain_size = free_asize - asize;
    delete_block(bp);
    // 如果剩余块大小小于最小块大小，则不分割
    if (remain_size < FREE_BLOCK_MIN) {
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
        void *next_p = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(remain_size, GET_PREV_ALLOC(HDRP(bp)) | 0));
        PUT(FTRP(bp), PACK(remain_size, GET_PREV_ALLOC(HDRP(bp)) | 0));
        // 次低位（上一个块为分配块）设置为1，最低位（当前块为分配块）设置为0
        SET_PREV_ALLOC(HDRP(next_p));
        // 设置分配块的头部和脚部
        new_bp = NEXT_BLKP(bp);
        PUT(HDRP(new_bp), PACK(asize, 0b01));
        PUT(FTRP(new_bp), PACK(asize, 0b01));
        // PUT(HDRP(NEXT_BLKP(bp)), PACK(remain_size, 0b10));
        // PUT(FTRP(NEXT_BLKP(bp)), PACK(remain_size, 0b10));
        // 将下一个块插入空闲链表
        insert_block(bp);
    }
    return new_bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    #ifdef DEBUG
        printf("*** freeing...\n");
        if (mem_heapsize() == 854584 && GET_SIZE(HDRP(bp)) == 4080){
            printf("1");
        }
        // if (mem_heapsize() == 4350208){
        //     printf("1");
        // }
        _check_heap();
    #endif
    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACK(size, prev_alloc | 0));
    PUT(FTRP(bp), PACK(size, prev_alloc | 0));
    coalesce(bp);   
}

static void *coalesce(void *bp)
{
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
            // printf("the info of bp is %p\n", bp);
            // printf("prev: %p, size: %d\n", GET_PREV(bp), GET_SIZE(HDRP(GET_PREV(bp))));
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
        printf("*** mallocing blocks...\n");
        if ((1891880) <= (int)mem_heapsize()){ // 1891887
            printf("%d\n", (int)mem_heapsize());
        }
    #endif
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp = NULL;
    
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= WSIZE + 2 * DSIZE)
        asize = FREE_BLOCK_MIN;
    else // 只需要存header，不需要存footer
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE);

    asize = adjust_alloc_size(asize);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        bp = place(bp, asize);
        // return bp;
    }else{
        extendsize = MAX(asize, CHUNKSIZE);
        #ifdef DEBUG
            if (((int)mem_heapsize() == 1891888 - 4128) || 0
                // ((void *)bp + GET_SIZE(HDRP(bp)) <= (void *)mem_heap_hi() + 1)
                ){
                printf("1");   
            }
        #endif 
        if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
            return NULL;
        assert((void *)bp + GET_SIZE(HDRP(bp)) <= (void *)mem_heap_hi() + 1);
        bp = place(bp, asize);
    }

    /* No fit found. Get more memory and place the block */
    return bp;
}

void *mm_realloc(void *ptr, size_t size){
    #ifdef DEBUG
        printf("*** reallocing blocks...\n");
    #endif

    if (ptr == NULL) {
        return mm_malloc(size);
    }
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(ptr));
    size_t asize = MAX(
        FREE_BLOCK_MIN,
        DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE)
    );

    if (asize <= oldsize){
        return ptr;
    }

    void* newptr;

    if (NEXT_BLKP(ptr) == mem_heap_hi() + 1){
        size_t copySize;
        newptr = mm_malloc(size);
        if (newptr == NULL)
        return NULL;
        copySize = GET_SIZE(HDRP(newptr));
        copySize = MIN(copySize, oldsize);
        memmove(newptr, ptr, copySize - WSIZE);
        mm_free(ptr);
        return newptr; 
    }

    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))){
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        size_t prev_alloc = GET_PREV_ALLOC(HDRP(ptr));
        size_t total_size = oldsize + next_size;
        void * next_free = NEXT_BLKP(ptr);
        if (total_size - asize >= FREE_BLOCK_MIN){
            delete_block(next_free);
            PUT(HDRP(ptr), PACK(asize, prev_alloc | 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(total_size - asize, 0b10));
            PUT(FTRP(NEXT_BLKP(ptr)), PACK(total_size - asize, 0b10));
            insert_block(NEXT_BLKP(ptr));   
            // if (NEXT_BLKP(ptr) == pre_listp){
            //     pre_listp = ptr;
            // }
            // place(ptr, adjust_size);
            return ptr;
        }
    }

    
    size_t copySize;
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(newptr));
    copySize = MIN(copySize, oldsize);
    memmove(newptr, ptr, copySize - WSIZE);
    mm_free(ptr);
    return newptr;
}

#ifdef DEBUG

static void show_block(void *bp){
    printf("==========================================\n");
    printf("bp is %p\n", bp);
    printf("size is %d\n", GET_SIZE(HDRP(bp)));
    printf("alloced? %d\n", GET_ALLOC(HDRP(bp)));
    if (!GET_PREV_ALLOC(HDRP(bp))){
        printf("prev block is %p\n", PREV_BLKP(bp));
    }else{
        printf("prev block is alloced\n");
    }
    printf("next block is %p\n", NEXT_BLKP(bp));
    if (!GET_ALLOC(HDRP(bp))){
        printf("next free: %p\n", GET_NEXT(bp));
        printf("prev free: %p\n", GET_PREV(bp));
    }
    printf("==========================================\n");
}

static void print_heap(){
    printf("==========================================\n");
    printf("Heap Layout:\n");
    void* head = heap_listp;
    while (GET_SIZE(HDRP(head)) > 0)
    {
        printf("Block at %p, size %zu, alloced %d\n", head, GET_SIZE(HDRP(head)), GET_ALLOC(HDRP(head)));
        head = NEXT_BLKP(head);
    }
    printf("==========================================\n");
}

static void show_linklist(){
    for (int i = 0; i < NUM_LISTS; i++) {
        void *head = base_listp + i * DSIZE;
        void *current = GET_NEXT(head);
        if (current == NULL) continue;  
        printf("list %d: ", i);
        while (current != NULL) {
            unsigned long val = (unsigned long)current;
            printf("%d(%x) -> ", GET_SIZE(HDRP(current)), (val & 0xffff));
            current = GET_NEXT(current);
        }
        printf("\n");
    }
}

static void show_basic(){
    printf("current heap_size: %d\n", (int)mem_heapsize());
    printf("current heap_hi: %p\n", (void *)mem_heap_hi() + 1);
}

static void _check_heap(){
    void *head = heap_listp;
    while (head != mem_heap_hi() + 1)
    {
        if (GET_SIZE(HDRP(head)) == 0){
            printf("1");
        }
        if (!GET_ALLOC(HDRP(head)) && (GET_SIZE(HDRP(head)) != GET_SIZE(FTRP(head)))){
            printf("error: %p\n", head);
        }
        head = NEXT_BLKP(head);
    }
}

#endif 