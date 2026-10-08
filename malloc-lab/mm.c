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

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 상수 매크로
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define PSIZE sizeof(void *)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define GET_PTR(p) (*(void **)(p))
#define PUT_PTR(p, val) (*(void **)(p) = (val))

#define GET_PRED(bp) (GET_PTR(bp))
#define GET_SUCC(bp) (GET_PTR((char *)(bp) + PSIZE))
#define SET_PRED(bp, val) (PUT_PTR((bp), val))
#define SET_SUCC(bp, val) (PUT_PTR(((char *)(bp) + PSIZE), val))

static char *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static char *free_listp;
static void *rover;

void insert_free(void *bp)
{
    SET_SUCC(bp, free_listp);
    SET_PRED(bp, NULL);

    if (free_listp != NULL)
    {
        SET_PRED(free_listp, bp);
    }

    free_listp = bp;

    if (rover == NULL)
        rover = bp;
}
void remove_free(void *bp)
{
    if (bp == rover)
    {
        rover = GET_SUCC(bp);
    }

    if (GET_PRED(bp) == NULL)
    {
        free_listp = GET_SUCC(bp);
        if (free_listp != NULL)
            SET_PRED(free_listp, NULL);
    }

    else if (GET_SUCC(bp) == NULL)
    {
        SET_SUCC(GET_PRED(bp), NULL);
        SET_PRED(bp, NULL);
    }

    else
    {
        SET_SUCC(GET_PRED(bp), GET_SUCC(bp));
        SET_PRED(GET_SUCC(bp), GET_PRED(bp));
    }

    if (rover == NULL)
        rover = free_listp;
}

int mm_init(void)
{
    free_listp = NULL;
    rover = NULL;

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + 1 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));
    heap_listp += 2 * WSIZE;

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

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
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

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

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

static void *coalesce(void *bp) // 반복되는 코드 최적화 필요
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

// best_fit
static void *find_fit(size_t asize)
{
    void *bp;
    void *best_bp = NULL;
    size_t best_size = (size_t)-1;  // 최댓값으로 초기화

    for (bp = free_listp; bp != NULL; bp = GET_SUCC(bp))
    {
        size_t csize = GET_SIZE(HDRP(bp));
        if (asize <= csize)
        {
            if (csize == asize) {
                return bp;  // 딱 맞으면 바로 반환 (더 찾아볼 필요 없음)
            }
            if (csize < best_size) {
                best_size = csize;
                best_bp = bp;
            }
        }
    }
    return best_bp;  // 못 찾으면 NULL
}

// 분할 배치
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_free(bp);
    if ((csize - asize) >= (2 * PSIZE + 2 * WSIZE))
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

void *mm_realloc(void *bp, size_t size)
{
    if (bp == NULL)
    {
        return mm_malloc(size);
    }
    if (size == 0)
    {
        mm_free(bp);
        return NULL;
    }
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));

    size_t oldsize = GET_SIZE(HDRP(bp));
    size_t asize;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if (oldsize >= asize)
    {
        if (oldsize - asize >= 2 * PSIZE + 2 * WSIZE)
        {
            void *next_bp;

            // 앞부분: allocated
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            next_bp = NEXT_BLKP(bp);

            // 뒷부분: free
            PUT(HDRP(next_bp), PACK(oldsize - asize, 0));
            PUT(FTRP(next_bp), PACK(oldsize - asize, 0));
            coalesce(next_bp);
        }
        return bp;
    }
    else
    {
        if (!next_alloc && oldsize + next_size >= asize)
        {
            size_t csize = oldsize + next_size;

            remove_free(NEXT_BLKP(bp));

            if (csize - asize >= 2 * PSIZE + 2 * WSIZE)
            {
                // 현재 bp는 allocated
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));

                // 남는 부분
                void *remainder = NEXT_BLKP(bp);

                PUT(HDRP(remainder), PACK(csize - asize, 0));
                PUT(FTRP(remainder), PACK(csize - asize, 0));
                coalesce(remainder);
            }
            else
            {
                PUT(HDRP(bp), PACK(csize, 1));
                PUT(FTRP(bp), PACK(csize, 1));
            }
            return bp;
        }
        else
        {
            void *newbp = mm_malloc(size); // 새로 할당된 공간의 시작주소 반환

            if (newbp == NULL)
                return NULL;
            // 뒤 블록 확인
            memcpy(newbp, bp, oldsize - DSIZE);
            mm_free(bp);
            return newbp;
        }
    }
}