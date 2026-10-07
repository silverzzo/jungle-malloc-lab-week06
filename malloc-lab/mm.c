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
    ""};
    
// 8바이트 정렬 기준
#define ALIGNMENT 8

// 크기를 8의 배수로 올림
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// size_t 크기를 8의 배수로 맞춘 값
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 상수 매크로
#define WSIZE 4             // 워드 크기 = 4B (header/footer 크기)
#define DSIZE 8             // 더블워드 크기 = 8B
#define CHUNKSIZE (1 << 12) // 힙을 확장할 때 기본적으로 늘리는 크기 = 4KB
#define PSIZE sizeof(void *)

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 둘 중 큰 값

#define PACK(size, alloc) ((size) | (alloc))                            // 크기랑 할당여부 합쳐서 header/footer에 저장할 값 생성
#define GET(p) (*(unsigned int *)(p))                                   // p가 가리키는 곳의 4B 값 읽기
#define PUT(p, val) (*(unsigned int *)(p) = (val))                      // p가 가리키는 곳에 4B 값 쓰기
#define GET_SIZE(p) (GET(p) & ~0x7)                                     // header/footer에서 블록 크기만 추출
#define GET_ALLOC(p) (GET(p) & 0x1)                                     // header/footer에서 할당 여부 추출 (0: free, 1: allocated)
#define HDRP(bp) ((char *)(bp) - WSIZE)                                 // 현재 블록의 header 주소
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)            // 현재 블록의 footer 주소
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블럭의 payload 주소
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블럭의 payload 주소

// 포인터용 읽기/쓰기 매크로
#define GET_PTR(p) (*(void **)(p))
#define PUT_PTR(p, val) (*(void **)(p) = (val))

// 명시적 가용 리스트 매크로
#define GET_PRED(bp) (GET_PTR(bp))                   // 이전 노드 - bp가 가리키는 곳에서 포인터 읽어옴
#define GET_SUCC(bp) (GET_PTR((char *)(bp) + PSIZE)) // 다음 노드 - bp + PSIZE 위치에서 포인터 읽어옴
#define SET_PRED(bp, val) (PUT_PTR((bp), val))
#define SET_SUCC(bp, val) (PUT_PTR(((char *)(bp) + PSIZE), val))

static char *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static char *free_listp; // free list 관리하는 전역변수

// 함수 두 개  - 리스트에 삽입/삭제
void insert_free(void *bp)
{
    SET_SUCC(bp, free_listp); // 넣으려는 블록의 다음값을 현재 프리리스트 포인터의 값으로
    SET_PRED(bp, NULL);       // 넣으려는 블록의 이전값은 NULL

    if (free_listp != NULL)
    {                             // 프리리스트의 값이 NULL이 아니면
        SET_PRED(free_listp, bp); // 현재 프리리스트의 값을 현재 넣으려는 블록으로 세팅
    }

    free_listp = bp; // 프리리스트가 현재 넣으려는 블록 가리킴
}
void remove_free(void *bp)
{
    // 맨 앞 제거
    if (GET_PRED(bp) == NULL)
    {
        free_listp = GET_SUCC(bp);
        if (free_listp != NULL)
            SET_PRED(free_listp, NULL);
    }

    // 맨 뒤 제거
    else if (GET_SUCC(bp) == NULL)
    {
        SET_SUCC(GET_PRED(bp), NULL);
        SET_PRED(bp, NULL); // 없어도 됨
    }

    // 중간 제거
    else
    {
        SET_SUCC(GET_PRED(bp), GET_SUCC(bp));
        SET_PRED(GET_SUCC(bp), GET_PRED(bp));
    }
}

/*  Padding, Prologue, Epilogue
    관리용 구조 생성,extend_heap()으로 실제 free block을 추가 */
int mm_init(void)
{
    free_listp = NULL; //free block이 하나도 없으니까 free list도 빈 상태에서 시작

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                          // 패딩
    PUT(heap_listp + 1 * WSIZE, PACK(DSIZE, 1)); // 프롤로그 헤더
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1)); // 프롤로그 푸터
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));     // 에필로그 헤더
    heap_listp += 2 * WSIZE;

    // extend_heap 호출해서 첫 free block을 만듦
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // free block header/footer,epilogue header 초기화
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp); // 이전 블록 free상태이면 병합
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 맞는 가용블럭 찾기
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    // 못 찾았으면 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
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

static void *coalesce(void *bp) //반복되는 코드 최적화 필요
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        insert_free(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc)
    {
        remove_free(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        insert_free(bp);
    }

    else if (!prev_alloc && next_alloc)
    {
        remove_free(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_free(bp);
    }

    else
    {
        remove_free(NEXT_BLKP(bp));
        remove_free(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_free(bp);
    }
    return bp;
}

// first_fit
static void *find_fit(size_t asize)
{
    void *bp;

    /* bp를 free_listp에서 시작;
       블록크기가 0보다 큰동안(에필로그 블록 전까지) 반복하면서;
       다음블록으로 이동
    */
    for (bp = free_listp; bp!=NULL; bp = GET_SUCC(bp))
    {
        if (asize <= GET_SIZE(HDRP(bp)))
        {
            return bp;
        }
    }
    return NULL;
}

// 분할 배치
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_free(bp);
    if ((csize - asize) >= (2*PSIZE + 2*WSIZE))
    {
        
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);

        
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        insert_free(bp);

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
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}