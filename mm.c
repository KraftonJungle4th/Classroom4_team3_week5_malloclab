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
#define CHUNKSIZE (1<<12)  // 1<<15
#define BUDDY 20

#define MAX(x, y) (x > y ? x : y)

#define PACK(size, alloc) (size | alloc)

#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))

#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp)    ((char *)(bp) - WSIZE) // 헤더,포인터2개
//#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더,푸터,포인터2개  

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define GET_SUCC(bp) (*(void **)(bp)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)((bp) + WSIZE))  
#define GET_ROOT(class) (*(void **)((void *)(heap_listp) + (class * WSIZE)))

static void *heap_listp;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);

static void add_free_block(void *bp);
static void remove_free_block(void *ptr);
static int get_class(size_t size);


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk((BUDDY + 4) * WSIZE)) == (void *)-1){
        return -1;
    }
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK((BUDDY + 2)* WSIZE, 1)); // 버디+헤더+푸터
    for (int i=0; i<BUDDY; i++){
        PUT(heap_listp + ((2+i) * WSIZE), NULL);
    }
    PUT(heap_listp + ((2 + BUDDY)* WSIZE), PACK((BUDDY + 2)* WSIZE, 1)); // footer
    PUT(heap_listp + ((3 + BUDDY)* WSIZE), PACK(0, 1));
    
    heap_listp += (2*WSIZE); // 첫번째 버디 클래스를 가리킴

    if (extend_heap(4) == NULL)
        return -1;
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize = 16;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    while(asize < size + DSIZE){ // 요청받은 것보다 기본이 작으면 늘려줌
        asize <<= 1;
    }

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
    //PUT(FTRP(bp), PACK(size, 0));
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
    //size_t size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 홀수 맞출 필요 X

    if ((long)(bp = mem_sbrk(words * WSIZE)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(words * WSIZE, 0));
    //PUT(FTRP(bp), PACK(words * WSIZE, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 블록

    return coalesce(bp);    
}

static void *coalesce(void *bp)
{
    add_free_block(bp);

    size_t csize = GET_SIZE(HDRP(bp));
    void *root = heap_listp + (BUDDY + 1) * WSIZE; // 버디 + 푸터 만큼
    void *left, *right;

    while (1) {

        if ((bp - root) & csize){
            right = bp;
            left = bp - csize;
        }
        else{
            left = bp;
            right = bp + csize;
        }

        if (!GET_ALLOC(HDRP(left)) && !GET_ALLOC(HDRP(right))
            && GET_SIZE(HDRP(left)) == GET_SIZE(HDRP(right))){ // 둘 다 free면 합칠 수 있음
            remove_free_block(left);
            remove_free_block(right);
            csize <<= 1;
            PUT(HDRP(left), PACK(csize, 0));
            add_free_block(left);
            bp = left;
        }
        else
            break;
    }

    return bp;
}

static void *find_fit(size_t asize) // first fit
{
    void *bp;
    int class;

    for (class = get_class(asize); class < BUDDY; class++){
        for (bp = GET_ROOT(class); bp != NULL; bp = GET_SUCC(bp)){
            if(GET_SIZE(HDRP(bp)) >= asize){
                return bp;
            }
        }
    }
    return NULL;
}

static int get_class(size_t size){
    int list = 0;
    
    while(list < BUDDY - 1 && size > 1){
        size >>= 1;
        list++;
    }

    return list;
}

static void place(void *bp, size_t asize)
{
    remove_free_block(bp);
    size_t csize = GET_SIZE(HDRP(bp));
    
    while (asize != csize) { // 
        csize >>= 1;
        PUT(HDRP(bp + csize), PACK(csize, 0));
        add_free_block(bp+csize);
    }
    PUT(HDRP(bp), PACK(csize, 1));
}

static void remove_free_block(void *ptr)
{
    int class = get_class(GET_SIZE(HDRP(ptr)));

    if (ptr == GET_ROOT(class)){
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class));
        return;
    }

    GET_SUCC(GET_PRED(ptr)) = GET_SUCC(ptr); // 앞뒤 연결해주기
    if (GET_SUCC(ptr) != NULL)
        GET_PRED(GET_SUCC(ptr)) = GET_PRED(ptr);

    //printf("alloc %d\n", class);
}

static void add_free_block(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));
    GET_SUCC(bp) = GET_ROOT(class);
    if (GET_ROOT(class) != NULL)
        GET_PRED(GET_ROOT(class)) = bp;
    GET_ROOT(class) = bp;

    //printf("free %d\n", class);
}