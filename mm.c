#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "3team",
    "Indwoo",
    "jiu05042995@gmail.com",
    "",
    ""};

#define WSIZE 4             // header/footer 사이즈 4bytes
#define DSIZE 8             // 더블 워드 사이즈 8bytes
#define CHUNKSIZE (1 << 12) // 이 크기 만큼 힙을 확장(bytes)

#define MAX(x, y) (x > y ? x : y)

// 크기와 할당 비트를 통합하여 header/footer에 저장할 수 있는 값을 1워드로 리턴한다.
#define PACK(size, alloc) ((size) | (alloc))

// p가 참조하는 워드를 읽어서 리턴
#define GET(p) (*(unsigned int *)(p))

// p가 가리키는 워드에 val 저장
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))

// 주소 p에 있는 header/footer의 size와 할당 bit 리턴
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp는 데이터 시작 지점을 가리키고 있으므로 1워드만큼 앞으로 가면 header가 나온다
#define HDRP(bp) ((char *)(bp)-WSIZE)

/* 포인터를 헤더로 옮기고 사이즈를 가져온 뒤, 사이즈만큼 뒤로 간다.
    이후 헤드와 푸터를 제외한 만큼 앞으로 가면 footer가 나온다.*/
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음과 이전 블록의 블록 포인터 리턴
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

// for explicit
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소

// for implicit
static void *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void splice_free_block(void *bp); // 가용 리스트에서 제거
static void add_free_block(void *bp);    // 가용 리스트에 추가

int mm_init(void)
{
    // 8워드 크기의 힙 생성, heap_listp에 힙의 시작 주소값 할당
    if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(2 * WSIZE, 1)); // Prologue Header
    PUT(heap_listp + (2 * WSIZE), PACK(2 * WSIZE, 1)); // Prologue Footer
    PUT(heap_listp + (3 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 header
    PUT(heap_listp + (4 * WSIZE), NULL);               // 이전 가용 블록의 주소
    PUT(heap_listp + (5 * WSIZE), NULL);               // 다음 가용 블록의 주소
    PUT(heap_listp + (6 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 footer
    // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄
    PUT(heap_listp + (7 * WSIZE), PACK(0, 1));

    heap_listp += (4 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

// 새 가용 블록으로 힙 확장하기(힙이 초기화되거나 malloc이 적당한 맞춤 fit을 찾지 못했을 때)
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    ////////////////////////////////////////////////////////////////////////////////////////////
    // 정렬 유지 위해 요청한 크기를 인접 2워드 배수(8바이트)로 반올림 하여 추가적인 힙 공간을 요청한다.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    ////////////////////////////////////////////////////////////////////////////////////////////

    PUT(HDRP(bp), PACK(size, 0));         // 전달받은 size의 크기(2워드 배수)만큼 새 가용 블록의 header
    PUT(FTRP(bp), PACK(size, 0));         // 새 가용 블록의 footer.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // heap공간이 추가되었으므로 epilouge의 새로운 header가 된다.

    return coalesce(bp); // 이전 힙이 가용블록으로 끝났으면 두 가용 블록을 합하기 위해 함수 호출, 통합된 블록의 블록 포인터 리턴
}

void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0)); // header에 할당받았던 사이즈와 정보가 없다는 0 정보를 넣어둠
    PUT(FTRP(ptr), PACK(size, 0)); // footer에 할당받았던 사이즈와 정보가 없다는 0 정보를 넣어둠
    coalesce(ptr);
}

static void *coalesce(void *bp)
{
    // 이전 블록의 블록 포인터의 footer를 받음
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));

    // 다음 블록의 블록 포인터의 header를 받음
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    // 지금 블록의 헤더포인터에서 사이즈를 가져옴
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) // 이전과 다음 블록이 모두 할당된 상태
    {
        add_free_block(bp); // free_list에 추가
        return bp;
    }
    else if (prev_alloc && !next_alloc) // 이전 블록은 할당, 다음 블록은 가용(비어있는)상태
    {
        splice_free_block(NEXT_BLKP(bp));      // 가용한 다음 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 header에서 사이즈를 가져와서 더함
        PUT(HDRP(bp), PACK(size, 0));          // 현재 bp header에 가용된 블록의 사이즈만큼 갱신함
        PUT(FTRP(bp), PACK(size, 0));          // 현재 bp footer에 가용된 블록의 사이즈만큼 갱신함
        add_free_block(bp);                    // 현재 병합한 가용 블록을 free_list에 추가
        return bp;
    }
    else if (!prev_alloc && next_alloc) // 이전 블록은 가용, 다음 블록은 할당된 상태
    {
        splice_free_block(PREV_BLKP(bp));        // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 이전 블록의 header에서 사이즈를 가져와서 더함
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 현재 bp가 가리키는 이전 블록의 bp의 header에 size 정보를 갱신함
        PUT(FTRP(bp), PACK(size, 0));            // 현재 bp footer에 가용된 블록의 사이즈만큼 갱신함
        bp = PREV_BLKP(bp);                      // bp를 이전 블록의 bp로 갱신함
        add_free_block(bp);                      // 현재 병합한 가용 블록을 free_list에 추가
        return bp;
    }
    else // 이전과 다음 블록이 모두 가용한 상태
    {
        splice_free_block(PREV_BLKP(bp)); // 이전 가용 블록을 free_list에서 제거
        splice_free_block(NEXT_BLKP(bp)); // 다음 가용 블록을 free_list에서 제거
        // 이전 블록의 header에서 가져온 사이즈 + 다음 블록의 footer에서 가져온 사이즈를 더함
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 현재 bp의 이전 블록의 header 포인터에 size 정보 갱신함
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 현재 bp의 다음 블록의 footer 포인터에 size 정보 갱신함
        bp = PREV_BLKP(bp);                      // bp를 이전 블록의 bp로 갱신함
        add_free_block(bp);                      // 현재 병합한 가용 블록을 free_list에 추가
        return bp;
    }
    
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE) // 최소 16바이트 크기 블록 구성(정렬 요건을 위한 8바이트 + header와 footer 8바이트)
        asize = 2 * DSIZE;
    else
        // 16바이트보다 큰 경우 header footer 8바이트 + 인접한 8의 배수 만큼 할당
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) // 적절한 가용 블록을 가용 리스트에서 검색
    {
        place(bp, asize); // 요청한 블록 배치, 옵션으로 초과 부분 분할, 새롭게 할당한 블록 리턴
        return bp;
    }

    // 할당기가 맞는 블록을 찾지 못하면 힙을 새로운 가용 블록으로 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;

    /*int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else
    {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
    */
}

static void *find_fit(size_t asize)
{
    void *bp = heap_listp;
    while (bp != NULL) // 다음 가용 블럭이 있는 동안 반복
    {
        if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
            return bp;
        bp = GET_SUCC(bp); // 다음 가용 블록으로 이동
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    splice_free_block(bp); // free_list에서 해당 블록 제거

    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기(16)보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK(csize - asize, 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));
        add_free_block(NEXT_BLKP(bp)); // 남은 블록을 free_list에 추가
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


void *mm_realloc(void *ptr, size_t size)
{
    /* 예외 처리 */
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
        return mm_malloc(size);

    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(ptr);
        return 0;
    }

    /* 새 블록에 할당 */
    void *newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
    if (newptr == NULL)
        return NULL; // 할당 실패

    /* 데이터 복사 */
    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload만큼 복사
    if (size < copySize)                           // 기존 사이즈가 새 크기보다 더 크면
        copySize = size;                           // size로 크기 변경 (기존 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사)

    memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사

    /* 기존 블록 반환 */
    mm_free(ptr);

    return newptr;
}

// 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수
static void splice_free_block(void *bp)
{
    if (bp == heap_listp) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        heap_listp = GET_SUCC(heap_listp); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);

    // 다음 가용 블록이 있을 경우만 다음 블록의 PRED를 이전 블록으로 변경
    if (GET_SUCC(bp) != NULL)
    {
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
    }
}

// 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수
static void add_free_block(void *bp)
{
    GET_SUCC(bp) = heap_listp;     // bp의 SUCC은 루트가 가리키던 블록
    if (heap_listp != NULL)        // free list에 블록이 존재했을 경우만
        GET_PRED(heap_listp) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    heap_listp = bp;               // 루트를 현재 블록으로 변경
}