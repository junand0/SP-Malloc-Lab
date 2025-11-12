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

 /* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define FREE_LIST_NUM 15
#define PAGE_SIZE (1 << 12)
#define INIT_SIZE (1 << 6)
#define SPLIT_MIN_SIZE 16
#define REALLOC_BUFF_SIZE (1 << 6)
#define FREE_LIST_MIN_SIZE DSIZE

#define PACK(size, alloc) (size | alloc) // pack size with alloc flag
#define GET_SIZE(hp) (*(size_t *)hp & ~0x7)
#define GET_ALLOC(hp) (*(size_t *)hp & 0x1)
#define HDRP(bp) ((size_t *)((char *)bp - WSIZE))
#define FTRP(bp) ((size_t *)((char *)bp + GET_SIZE(HDRP(bp)) - DSIZE))

#define PUT_W(p, val) (*(size_t *)p = val)

// free list nodes
#define PREV_BLOCK_PTR(p) ((char **)p)
#define PREV_BLOCK(p) ((char *)(*PREV_BLOCK_PTR(p)))
#define NEXT_BLOCK_PTR(p) ((char **)((char *)p + WSIZE))
#define NEXT_BLOCK(p) ((char *)(*NEXT_BLOCK_PTR(p)))

// neighborhood blocks
#define PRED_BLOCK_FTRP(bp) ((size_t *)((char *)bp - DSIZE))
#define SUCC_BLOCK(bp) ((char *)bp + GET_SIZE(HDRP(bp)))
#define PRED_BLOCK(bp) ((char *)bp - GET_SIZE(PRED_BLOCK_FTRP(bp)))

#define MAX(x, y) (x > y ? x : y)
#define MIN(x, y) (x < y ? x : y)

void* free_list_array[FREE_LIST_NUM];

void* find_fit_free_block(size_t asize);
void* extend_heap(size_t size);
int get_free_list_index(void* p);
void add_free_node(void* p);
void withdraw_free_node(void* p);
void set_tag(void* bp, size_t size, int is_allocated);
void* coalesce(void* bp);
void* place(void* bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    for (int i = 0; i < FREE_LIST_NUM; i++)
    {
        free_list_array[i] = NULL;
    }

    void* p = mem_sbrk(WSIZE * 4);
    if (p == (void*)-1)
        return -1;

    PUT_W(p, 0);                                    // For 8 byte alignment of payload pointer
    set_tag(((char*)p + WSIZE), DSIZE, 1);         // Prologue
    PUT_W(((char*)p + WSIZE + DSIZE), PACK(0, 1)); // Epilogue

    void* init_break = extend_heap(INIT_SIZE);
    if (init_break == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void* mm_malloc(size_t size)
{
    if (size == 0)
        return NULL;

    int asize = ALIGN(size + DSIZE);
    void* free_block = find_fit_free_block(asize);
    if (free_block)
    {
        return place(free_block, asize);
    }

    size_t extend_size = MAX(asize, PAGE_SIZE);
    void* bp = extend_heap(extend_size);
    if (bp == NULL)
        return NULL;

    return place(bp, asize);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void* ptr)
{
    size_t block_size = GET_SIZE(HDRP(ptr));
    set_tag(ptr, block_size, 0);
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void* mm_realloc(void* ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    size_t new_size = ALIGN(size + DSIZE) + REALLOC_BUFF_SIZE;
    size_t old_size = GET_SIZE(HDRP(ptr));

    if (old_size >= new_size)
    {
        return ptr;
    }

    void* newptr = ptr;
    void* succ_block_header = HDRP(SUCC_BLOCK(ptr));
    int is_succ_free = !GET_ALLOC(succ_block_header);
    int is_succ_epilogue = !GET_SIZE(succ_block_header);

    // If successor block is epilogue
    if (is_succ_epilogue) {
        size_t realloc_size = old_size + GET_SIZE(succ_block_header);
        if (realloc_size < new_size)
        {
            size_t extend_size = MAX(new_size - realloc_size, PAGE_SIZE);
            void* extend_p = extend_heap(extend_size);
            if (extend_p == NULL)
            {
                return NULL;
            }
            realloc_size = realloc_size + extend_size;
        }

        withdraw_free_node(SUCC_BLOCK(ptr));
        set_tag(newptr, realloc_size, 1);
    }
    // If successor block is free block
    else if (is_succ_free)
    {
        size_t realloc_size = old_size + GET_SIZE(succ_block_header);
        if (realloc_size < new_size)
        {
            size_t extend_size = MAX(new_size, PAGE_SIZE);
            void* extend_p = extend_heap(extend_size);
            if (extend_p == NULL)
            {
                return NULL;
            }

            realloc_size = extend_size;
            newptr = extend_p;
        }
        else {
            withdraw_free_node(SUCC_BLOCK(ptr));
        }
        set_tag(newptr, realloc_size, 1);
    }
    else {
        newptr = mm_malloc(new_size - DSIZE);
        if (newptr == NULL)
            return NULL;
        mm_free(ptr);
    }

    size_t copySize = MIN(old_size, new_size);
    memcpy(newptr, ptr, copySize);
    return newptr;
}

void* find_fit_free_block(size_t asize)
{
    int start_index = 0;
    for (size_t s = FREE_LIST_MIN_SIZE; s < asize; s <<= 1)
    {
        start_index++;
        if (start_index >= FREE_LIST_NUM - 1)
            break;
    }

    for (int i = start_index; i < FREE_LIST_NUM; i++)
    {
        void* free_block = free_list_array[i];
        while (free_block != NULL)
        {
            if (asize <= GET_SIZE(HDRP(free_block)))
            {
                return free_block;
            }
            free_block = NEXT_BLOCK(free_block);
        }
    }
    return NULL;
}

void* extend_heap(size_t size)
{
    size_t asize = ALIGN(size);
    void* bp = mem_sbrk(asize);
    if (bp == (void*)-1)
        return NULL;

    set_tag(bp, asize, 0);
    PUT_W(HDRP(SUCC_BLOCK(bp)), PACK(0, 1)); // Epilogue

    return coalesce(bp);
}

int get_free_list_index(void* p)
{
    const size_t size = GET_SIZE(HDRP(p));
    int list_index = 0;

    for (size_t s = FREE_LIST_MIN_SIZE; s < size; s <<= 1)
    {
        list_index++;
        if (list_index >= FREE_LIST_NUM - 1)
            break;
    }

    return list_index;
}

void add_free_node(void* p)
{
    int list_index = get_free_list_index(p);

    void* free_list_root = free_list_array[list_index];
    if (free_list_root == NULL)
    {
        *PREV_BLOCK_PTR(p) = NULL;
        *NEXT_BLOCK_PTR(p) = NULL;
        free_list_array[list_index] = p;
        return;
    }

    size_t size = GET_SIZE(HDRP(p));
    void* head = free_list_root;
    void* tail = NULL;
    while (head && size > GET_SIZE(HDRP(head)))
    {
        tail = head;
        head = NEXT_BLOCK(head);
    }

    if (tail == NULL)
    {
        *PREV_BLOCK_PTR(p) = NULL;
        *NEXT_BLOCK_PTR(p) = ((char*)head);
        *PREV_BLOCK_PTR(head) = ((char*)p);
        free_list_array[list_index] = p;
    }
    else if (head == NULL)
    {
        *PREV_BLOCK_PTR(p) = ((char*)tail);
        *NEXT_BLOCK_PTR(p) = NULL;
        *NEXT_BLOCK_PTR(tail) = ((char*)p);
    }
    else
    {
        *PREV_BLOCK_PTR(p) = ((char*)tail);
        *NEXT_BLOCK_PTR(p) = ((char*)head);
        *NEXT_BLOCK_PTR(tail) = ((char*)p);
        *PREV_BLOCK_PTR(head) = ((char*)p);
    }
}

void withdraw_free_node(void* p)
{
    int list_index = get_free_list_index(p);
    void* prev_free_block = PREV_BLOCK(p);
    void* next_free_block = NEXT_BLOCK(p);
    if (prev_free_block)
    {
        if (next_free_block)
        {
            *NEXT_BLOCK_PTR(prev_free_block) = next_free_block;
            *PREV_BLOCK_PTR(next_free_block) = prev_free_block;
        }
        else
        {
            *NEXT_BLOCK_PTR(prev_free_block) = NULL;
        }
    }
    else
    {
        if (next_free_block)
        {
            *PREV_BLOCK_PTR(next_free_block) = NULL;
            free_list_array[list_index] = next_free_block;
        }
        else
        {
            free_list_array[list_index] = NULL;
        }
    }
}

void set_tag(void* bp, size_t size, int is_allocated)
{
    PUT_W(HDRP(bp), PACK(size, is_allocated));
    PUT_W(FTRP(bp), PACK(size, is_allocated));
}

void* coalesce(void* bp)
{
    void* pred_block = PRED_BLOCK(bp);

    void* succ_block = SUCC_BLOCK(bp);
    void* succ_block_header = HDRP(succ_block);
    void* curr_block_header = HDRP(bp);

    size_t pred_size = GET_SIZE(PRED_BLOCK_FTRP(bp));
    size_t succ_size = GET_SIZE(succ_block_header);
    size_t curr_size = GET_SIZE(curr_block_header);
    int pred_block_coalescing = !GET_ALLOC(PRED_BLOCK_FTRP(bp)) && pred_size > DSIZE;
    int succ_block_coalescing = !GET_ALLOC(succ_block_header);

    void* coalesced_block = bp;

    if (pred_block_coalescing && succ_block_coalescing)
    {
        withdraw_free_node(pred_block);
        withdraw_free_node(succ_block);
        size_t new_size = pred_size + succ_size + curr_size;
        set_tag(pred_block, new_size, 0);
        coalesced_block = pred_block;
    }
    else if (pred_block_coalescing && !succ_block_coalescing)
    {
        withdraw_free_node(pred_block);
        size_t new_size = pred_size + curr_size;
        set_tag(pred_block, new_size, 0);
        coalesced_block = pred_block;
    }
    else if (!pred_block_coalescing && succ_block_coalescing)
    {
        withdraw_free_node(succ_block);
        size_t new_size = succ_size + curr_size;
        set_tag(bp, new_size, 0);
        coalesced_block = bp;
    }

    add_free_node(coalesced_block);
    return coalesced_block;
}

void* place(void* bp, size_t asize)
{
    size_t block_size = GET_SIZE(HDRP(bp));
    size_t redundant_size = block_size - asize;

    withdraw_free_node(bp);

    if (redundant_size < SPLIT_MIN_SIZE)
    {
        set_tag(bp, block_size, 1);
        return bp;
    }

    if (asize >= REALLOC_BUFF_SIZE + SPLIT_MIN_SIZE) {
        set_tag(bp, redundant_size, 0);
        set_tag(SUCC_BLOCK(bp), asize, 1);
        add_free_node(bp);
        return SUCC_BLOCK(bp);
    }

    set_tag(bp, asize, 1);
    set_tag(SUCC_BLOCK(bp), redundant_size, 0);
    add_free_node(SUCC_BLOCK(bp));
    return bp;
}