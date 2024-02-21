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
#define MAX(x, y) ((x) > (y) ? (x) : (y))
// 크기와 할당 비트를 통합하여 header/footer에 저장할 수 있는 값을 리턴한다.
#define PACK(size, alloc) ((size) | (alloc))
// p가 참조하는 워드를 읽어서 리턴
#define GET(p) (*(unsigned int *)(p))
// p가 가리키는 워드에 val 저장
#define PUT(p, val) (*(unsigned int *)(p) = (val))
// 주소 p에 있는 header/footer의 size와 할당 bit 리턴
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
// bp를 받아 블록의 header/footer 가리키는 포인터 리턴
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
// 다음과 이전 블록의 블록 포인터 리턴
#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) (((char *)(bp)-GET_SIZE((char *)(bp)-DSIZE)))
static void *heap_listp;
static char *recently_visited;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 빈 가용 리스트 Prologue Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 빈 가용 리스트 Prologue Footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 빈 가용 리스트 Epilouge header
    heap_listp += DSIZE;
    if (extend_heap(4) == NULL)
        return -1;
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
        recently_visited = bp;
        return bp;
    }
    else if (prev_alloc && !next_alloc) // 이전 블록은 할당, 다음 블록은 가용(비어있는)상태
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 header에서 사이즈를 가져와서 더함
        PUT(HDRP(bp), PACK(size, 0));          // 현재 bp header에 가용된 블록의 사이즈만큼 갱신함
        PUT(FTRP(bp), PACK(size, 0));          // 현재 bp footer에 가용된 블록의 사이즈만큼 갱신함
    }
    else if (!prev_alloc && next_alloc) // 이전 블록은 가용, 다음 블록은 할당된 상태
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 이전 블록의 header에서 사이즈를 가져와서 더함
        PUT(FTRP(bp), PACK(size, 0));            // 현재 bp footer에 가용된 블록의 사이즈만큼 갱신함
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 현재 bp가 가리키는 이전 블록의 bp의 header에 size 정보를 갱신함
        bp = PREV_BLKP(bp);                      // bp를 이전 블록의 bp로 갱신함
    }
    else // 이전과 다음 블록이 모두 가용한 상태
    {
        // 이전 블록의 header에서 가져온 사이즈 + 다음 블록의 footer에서 가져온 사이즈를 더함
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 현재 bp의 이전 블록의 header 포인터에 size 정보 갱신함
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 현재 bp의 다음 블록의 footer 포인터에 size 정보 갱신함
        bp = PREV_BLKP(bp);                      // bp를 이전 블록의 bp로 갱신함
    }
    recently_visited = bp;
    return bp;
}
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    if (size == 0)
        return NULL;
    if (size <= DSIZE) /// 사이즈가 DSIZE 이하면 4워드만큼 할당(외부 단편화 방지).
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    //////////////////////////////
    recently_visited = bp; // 현재 블록의 위치를 저장하여 find_fit에 사용
    //////////////////////////////
    return bp;
}
static void *find_fit(size_t asize) // next fit
{
    char *bp = recently_visited; // void *bp에서 변경
    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
        {
            recently_visited = bp;
            return bp;
        }
    }
    bp = heap_listp;
    while (bp < recently_visited)
    {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
        {
            recently_visited = bp;
            return bp;
        }
    }
    return NULL;
}
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= (2 * DSIZE))
    {
        // 요청한 크기만큼 블록 배치
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        // 남은 블록에 header와 footer 배치
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
//