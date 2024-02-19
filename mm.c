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
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))

#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp)    ((char *)(bp) - WSIZE) // 헤더,포인터2개
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더,푸터,포인터2개  

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define GET_SUCC(bp) (*(void **)(bp)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)((bp) + WSIZE))  

static void *heap_listp;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);

static void add_free_block(void *bp);
static void remove_free_block(void *ptr);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1)
        return -1;
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // footer
    PUT(heap_listp + (3*WSIZE), PACK(2*DSIZE, 0)); // header
    PUT(heap_listp + (4*WSIZE), NULL); // next ptr
    PUT(heap_listp + (5*WSIZE), NULL); // prev ptr
    PUT(heap_listp + (6*WSIZE), PACK(2*DSIZE, 0)); // footer
    PUT(heap_listp + (7*WSIZE), PACK(0, 1));
    
    heap_listp += (4*WSIZE);

    if (extend_heap(4) == NULL)
        return -1;
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2*DSIZE;
    else   
        asize = DSIZE * ((size + DSIZE + DSIZE-1) / DSIZE);

    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    return bp;
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);

    if (size <= 0){
        mm_free(ptr);
        return 0;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    size_t copysize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if (size < copysize)
        copysize = size;

    memcpy(newptr, ptr, copysize);
    mm_free(ptr);
    return newptr;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 블록

    return coalesce(bp);    
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // if (prev_alloc && next_alloc){ // Case1 앞뒤가 이미 할당됨
    
    if (prev_alloc && !next_alloc){ // Case2 뒤가 free
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){ // Case3 앞이 free
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc){ // Case4 앞뒤 모두 free
        remove_free_block(NEXT_BLKP(bp));
        remove_free_block(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    add_free_block(bp);
    return bp;

}

static void *find_fit(size_t asize) // first fit
{
    void *bp;

    for (bp = heap_listp; bp != NULL; bp = GET_SUCC(bp)){
        if (GET_SIZE(HDRP(bp)) >= asize)
            return bp;
    }
    
    return NULL;
}

static void place(void *bp, size_t asize)
{
    remove_free_block(bp);
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        //bp = NEXT_BLKP(bp);
        PUT(HDRP(NEXT_BLKP(bp)), PACK((csize-asize), 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK((csize-asize), 0));
        add_free_block(NEXT_BLKP(bp));
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void remove_free_block(void *ptr)
{
    if (ptr == heap_listp){
        heap_listp = GET_SUCC(heap_listp);
        return;
    }

    GET_SUCC(GET_PRED(ptr)) = GET_SUCC(ptr); // 앞뒤 연결해주기
    if (GET_SUCC(ptr) != NULL)
        GET_PRED(GET_SUCC(ptr)) = GET_PRED(ptr);
}

static void add_free_block(void *bp)
{
    GET_SUCC(bp) = heap_listp;
    if (heap_listp != NULL)
        GET_PRED(heap_listp) = bp;
    heap_listp = bp;
}