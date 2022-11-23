/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * The min_block size for this final version is 16 bytes. Each block is 16 bytes
 *aligned. As for the free blocks, free block with min_block_size only has a
 *header and a next pointer while other free blocks with 32 bytes have a header,
 *a footer, a next pointer and a previous pointer. All allocated blocks have a
 *header and payload. I use the segregated free list to hold free blocks, using
 *the first-fit algorithm to find the suitable block for allocation.
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Your Name <andrewid@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * chunksize is the size to give when call mm_sbrk
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 10);

/**
 * by using alloc_mask, prev_alloc_mask and min_block_mask, we can get the
 * block's alloc status, previous block's alloc staus and whether previous block
 * is min_block.
 */
static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = (0x1) << 1;
static const word_t min_block_mask = (0x1) << 2;

/**
 * by maskingheader with size_mask, we can get the size of the block.
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block block_t;
struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;
    union {
        struct {
            block_t *next;
            block_t *previous;
        };
        char payload[0];
    } node;
};

/* build an array for free list*/
block_t *head[15];

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @param[in] prev_alloc True if the previous block is allocated
 * @param[in] min_alloc True if the previous block is min_block
 * @return The packed value
 */
static word_t pack(size_t size, bool min_alloc, bool prev_alloc, bool alloc) {
    word_t word = size;

    // block is allocated
    if (alloc) {
        // previous block is allocated
        if (prev_alloc) {
            // previous block is min_block
            if (min_alloc) {
                word |= (min_block_mask | (prev_alloc_mask | alloc_mask));
                // previous block is not min_block
            } else {
                word |= (prev_alloc_mask | alloc_mask);
            }
            // previous block is not allocated
        } else if (prev_alloc == false) {
            // previous block is min_block
            if (min_alloc) {
                word |= (min_block_mask | alloc_mask);
                // previous block is not min_block
            } else if (min_alloc == false) {
                word |= alloc_mask;
            }
        }
        // block is unallocated
    } else if (alloc == false) {
        // previous block is allocated
        if (prev_alloc) {
            // previous block is min_block
            if (min_alloc) {
                word |= (min_block_mask | prev_alloc_mask);
                // previous block is not min_block
            } else {
                word |= prev_alloc_mask;
            }
            // previous block is unallocated
        } else if (prev_alloc == false) {
            // previous block is min_block
            if (min_alloc) {
                word |= min_block_mask;
            }
        }
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, node.payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->node.payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->node.payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}
/**
 * @brief Returns previous block's allocation status of a given header value.
 *
 * This is based on the second lowest bit of the header value.
 *
 * @param[in] word
 * @return previous block's allocation status correpsonding to the word
 */

static bool extract_prev_alloc(word_t word) {
    return (bool)(word & prev_alloc_mask);
}

/**
 * @brief Returns whether previous block is a min_block.
 *
 * This is based on the third lowest bit of the header value.
 *
 * @param[in] word
 */
static bool extract_min_alloc(word_t word) {
    return (bool)(word & min_block_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Returns previous block's allocation status of a block, based on its
 * header.
 * @param[in] block
 * @return The allocation status of the previous block
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}

/**
 * @brief Returns whether previous block is min_block, based on its header.
 * @param[in] block
 */
static bool get_min_alloc(block_t *block) {
    return extract_min_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, false, false, true);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool min_alloc,
                        bool prev_alloc, bool alloc) {
    dbg_requires(block != NULL);
    /*
    dbg_requires(size > 0);
    */
    block->header = pack(size, min_alloc, prev_alloc, alloc);
    if (alloc == false) {
        if (size > min_block_size) {
            word_t *footerp = header_to_footer(block);
            *footerp = pack(size, min_alloc, prev_alloc, alloc);
        }
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {

    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines *********/

/**get the class of the specific segregated list according to block size.**
 * @param[in] size A block's size
 * @return The class in the segregated list that the block belongs to
 */
size_t get_class(size_t size) {
    if (size <= min_block_size) {
        return 0;
    } else if (size < (min_block_size * 1.5)) {
        return 1;
    } else if (size < (min_block_size * 2)) {
        return 2;
    } else if (size < (min_block_size * 3)) {
        return 3;
    } else if (size < (min_block_size * 4)) {
        return 4;
    } else if (size < (min_block_size * 6)) {
        return 5;
    } else if (size < (min_block_size * 8)) {
        return 6;
    } else if (size < (min_block_size * 16)) {
        return 7;
    } else if (size < (min_block_size * 32)) {
        return 8;
    } else if (size < (min_block_size * 64)) {
        return 9;
    } else if (size < (min_block_size * 128)) {
        return 10;
    } else if (size < (min_block_size * 256)) {
        return 11;
    } else if (size < (min_block_size * 512)) {
        return 12;
    } else if (size < (min_block_size * 1024)) {
        return 13;
    } else {
        return 14;
    }
    return 0;
}

/**insert a block in the free list.
 * first find the class the block belongs and then insert it
 * the first class(first free list in the segregated list) is a singly-linked
 * list, others are doubly-linked list
 * @param[in] block A block in the heap that is unallocated
 * @return nothing
 */
void insert(block_t *block) {
    if (block == NULL) {
        return;
    }
    // get the block's size and then the block's size
    size_t block_size = get_size(block);
    size_t class = get_class(block_size);

    // use singly-linked list for min_block
    if (class == 0) {
        if (head[0] == NULL) {
            head[0] = block;
            head[0]->node.next = head[0];
        } else {
            block_t *temp1 = head[0]->node.next;
            head[0]->node.next = block;
            block->node.next = temp1;
        }
        // use doubly-linked list for others
    } else {
        if (head[class] == NULL) {
            head[class] = block;
            head[class]->node.next = head[class];
            head[class]->node.previous = head[class];
        } else {
            block_t *temp1 = head[class]->node.next;
            head[class]->node.next = block;
            block->node.previous = head[class];
            block->node.next = temp1;
            temp1->node.previous = block;
        }
    }
}

/**delete a block in the free list.
 *@param[in] block A block in the heap that is switched from unallocated to
 *allocated
 * @return nothing
 */
void delete (block_t *block) {

    if (block == NULL) {
        return;
    }
    // get the block's size and then its class
    size_t block_size = get_size(block);
    size_t class = get_class(block_size);

    // delete a block in the singly-linked list
    if (class == 0) { // only one block in the list
        if (block->node.next == block) {
            head[0] = NULL;

        } else { // more than on block in the list
            block_t *head_min = head[0];
            block_t *prev = head[0];
            while (head_min->node.next != block) {
                head_min = head_min->node.next;
                prev = head_min;
            }
            prev->node.next = block->node.next;
            if (block == head[0]) { // if the block is the head, change the head
                head[0] = block->node.next;
            }
        }

        // delete a block in doubly-linked list
    } else {
        if (block->node.next == block) { // only one block in the list
            head[class] = NULL;
            return;
        } else { // more than one block in the list
            if (block->node.next != NULL) {
                if (block->node.previous != NULL) {
                    block->node.next->node.previous = block->node.previous;
                    block->node.previous->node.next = block->node.next;
                    if (block == head[class]) { // if the block is the head,
                                                // change the head
                        head[class] = block->node.next;
                    }
                }
            }
        }
    }
}

/**coalesce block with previous and next block, return the pointer of the
 * coalesced block.
 *@param[in] block A block in the heap that is switched from allocated to
 *unallocated
 * @return the coalesced block
 i*/
static block_t *coalesce_block(block_t *block) {

    if (block == NULL) {
        return NULL;
    }

    // get previous block's alloc status and min_block status
    bool previous_alloc = get_prev_alloc(block);
    bool prev_min = get_min_alloc(block);

    /*find previous_block and previous_size*/
    block_t *previous_block = NULL;
    size_t previous_size = 0;
    bool prev_prev_min = false;
    if (previous_alloc == false) {
        if (prev_min == true) { // if previous block is min_block, skip forward
                                // min_block_size bytes
            previous_block = (block_t *)((char *)block - min_block_size);
            if (previous_block != NULL) {
                previous_size = get_size(previous_block);
                prev_prev_min = get_min_alloc(previous_block);
            }
        } else { // if previous block is not min_block, use the find_prev()
                 // method
            previous_block = find_prev(block);
            if (previous_block != NULL) {
                previous_size = get_size(previous_block);
                prev_prev_min = get_min_alloc(previous_block);
            }
        }
    }

    /*find next block's alloc status and size*/
    block_t *next_block = find_next(block);

    size_t next_size = 0;
    bool next_alloc = true;
    if (next_block != NULL) {
        next_alloc = get_alloc(next_block);
        next_size = get_size(next_block);
    }

    // find next_next block and its size
    block_t *next_next_block = NULL;
    size_t next_next_size = 0;
    if (next_block != NULL && next_size != 0) {
        next_next_block = find_next(next_block);
        if (next_next_block != NULL) {
            next_next_size = get_size(next_next_block);
        }
    }

    /*find current block's size*/
    size_t current_block_size = 0;
    if (block != NULL) {
        current_block_size = get_size(block);
    }

    /*case1: both previous and next block are allocated.*/
    if (previous_alloc && next_alloc) {
        return block;
    }

    /*case2: previous block is not allocated and next is allocated */
    if ((!previous_alloc) && next_alloc) {

        if (previous_block != NULL) {
            size_t total_size = current_block_size + previous_size;
            write_block(previous_block, total_size, prev_prev_min, true, false);

            // update next block's status
            bool next_prev_min;
            if (total_size <= min_block_size) {
                next_prev_min = true;
            } else {
                next_prev_min = false;
            }
            write_block(next_block, next_size, next_prev_min, false, true);

            return previous_block;
        }
    }

    /*case3: previous is allocated and next block is not allocated.*/
    if (previous_alloc && (!next_alloc)) {

        size_t total_size = current_block_size + next_size;
        write_block(block, total_size, prev_min, true, false);

        // update next_next block
        bool next_next_prev_min;
        if (total_size <= min_block_size) {
            next_next_prev_min = true;
        } else {
            next_next_prev_min = false;
        }

        write_block(next_next_block, next_next_size, next_next_prev_min, false,
                    true);

        return block;
    }

    /*case4: both previous and next are not allocated*/
    if ((!previous_alloc) && (!next_alloc)) {

        if (previous_block != NULL) {
            size_t total_size = current_block_size + previous_size + next_size;
            write_block(previous_block, total_size, prev_prev_min, true, false);

            bool next_next_prev_min;
            if (total_size <= min_block_size) {
                next_next_prev_min = true;
            } else {
                next_next_prev_min = false;
            }

            write_block(next_next_block, next_next_size, next_next_prev_min,
                        false, true);
            return previous_block;
        }
    }

    return block;
}

/**
 * @brief extend the heap to at lest the given size with propoer alignment
 * @param[in] size
 * @return the pointer to the start of the big free block in the heap
 */
static block_t *extend_heap(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));
    void *bp;

    // allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    block_t *block = payload_to_header(bp);

    // find prev_alloc and prev_min
    bool prev_alloc = get_prev_alloc(block);
    bool prev_min = get_min_alloc(block);

    // if prev_alloc is true, write block without deleting previous block
    if (prev_alloc == true) {
        write_block(block, size, prev_min, true, false);

        // if prev_alloc is false, write block and delete previous block
    } else if (prev_alloc == false) {
        write_block(block, size, prev_min, false, false);

        if (prev_min ==
            true) { // cannot use find_prev(),skip min_block_size bytes forward
            block_t *previous_block =
                (block_t *)((char *)block - min_block_size);
            if (previous_block != NULL) {
                delete (previous_block); // delete previous block from free list
            }

        } else {
            block_t *previous_block = find_prev(block); // can use find_prev()

            if (previous_block != NULL) {
                delete (previous_block); // delete previous block from free list
            }
        }
    }

    // create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // coalesce if previous block was free.
    block = coalesce_block(block);
    insert(block);
    return block;
}

/**
 * @brief if the block size minus asize is larger than the min_block size, split
 * the block, change the block's alloc status to allocated, and insert the
 * remaining block to the free list.
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {

    dbg_requires(get_alloc(block));

    // find block's size and prev_min
    size_t block_size = get_size(block);
    bool prev_min = get_min_alloc(block);

    // split happens
    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, prev_min, true, true);

        // find next_block's prev_min bit
        bool next_prev_min;
        if (asize <= min_block_size) {
            next_prev_min = true;
        } else {
            next_prev_min = false;
        }

        // update next block and insert it into free list
        block_next = find_next(block);
        write_block(block_next, block_size - asize, next_prev_min, true, false);
        insert(block_next);

        // find next_next_block's prev_min bit
        bool next_next_prev_min;
        if (block_size - asize <= min_block_size) {
            next_next_prev_min = true;
        } else {
            next_next_prev_min = false;
        }

        // update next_next_block
        block_t *next_next_block = find_next(block_next);
        if (next_next_block != NULL) {
            size_t next_next_size = get_size(next_next_block);

            write_block(next_next_block, next_next_size, next_next_prev_min,
                        false, true);
        }

        // no split happens
    } else {

        block_t *next_block = find_next(block);
        bool next_prev_min = get_min_alloc(next_block);
        size_t next_size = get_size(next_block);
        write_block(next_block, next_size, next_prev_min, true, true);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief use the first_fit algorithm to find a block in the segregated list
 * whose size is equal or larger than asize.
 * @param[in] asize
 * @return the block whose size is equal to or larger than asize
 */
static block_t *find_fit(size_t asize) {
    // get the class in the segregated list according to asize
    size_t class = get_class(asize);
    block_t *block = head[class];

    while (class < 15) {
        // if the current list is empty, go to next list
        while (block == NULL && class < 14) {
            block = head[class + 1];
            class += 1;
        }
        // if no block is found, return NULL
        if (block == NULL) {
            return NULL;
        }
        // use to do-while loop to find a block whose size is equal or bigger
        // than asize. use the first-fit algorithm
        do {
            if (!(get_alloc(block)) && (asize <= get_size(block))) {
                return block;
            } else {
                block = block->node.next;
            }

        } while (block != head[class]);

        // if no block suitable in the current list, go to next free list
        block = head[class + 1];
        class += 1;
    }
    return NULL;
}

/**
 * @brief check wheather each block in the segregated list is in the size blound
 * of the class
 * @param[in] line
 * @return a boolean whether there is a block that is not in the size boud for
 * each list in the segregated list.
 */

/*check whether segregated list consistent with size_bound.*/
bool check_segregated_list_size_bound(int line) {
    size_t class = 0;
    block_t *block = head[class];
    while (class < 12) {
        while (block == NULL && class < 11) {
            block = head[class + 1];
            class += 1;
        }
        if (block == NULL) {
            return true;
        }
        do {
            size_t size = get_size(block);
            if (size >= (min_block_size * (1 << (class + 1)))) {
                dbg_printf("size bound unmatch class 1:%d\n", line);
                return false;
            } else {
                block = block->node.next;
            }
            block = block->node.next;

        } while (block != head[class]);
        block = head[class + 1];
        class += 1;
    }
    return true;
}

/**@brief check whether prev_alloc bit match prev_bloc
 *@param[in] line
 * @return a boolean whether prev_min_bit matched
 */
bool prev_min_bit(int line) {
    block_t *block;
    bool prev_min2;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {

        if (block != NULL) {
            block_t *next_block = find_next(block);
            bool prev_min1 = get_min_alloc(next_block);

            size_t size = get_size(block);
            if (size <= min_block_size) {
                prev_min2 = true;
            } else {
                prev_min2 = false;
            }
            if (prev_min1 != prev_min2) {
                dbg_printf("prev_min1 is unmatched with prev_min2\n");
                return false;
            }
            dbg_requires(prev_min1 == prev_min2 &&
                         "prev_min1 unmatched with prev_min2");
        }
    }
    bool prev_min_epilog1 = get_min_alloc(block);
    dbg_printf("iheck prev_min bit in epilog, prev_min_epilogue1 is:%d\n",
               prev_min_epilog1);
    dbg_printf("check prev_min bit in epilog, prev_min_epilogue2 is:%d\n",
               prev_min2);

    return true;
}

/**@brief check each block's alignment
 **@param[in] line
 * @return a boolean whether each block has proper alignment
 * */
bool check_pointer_alignment(int line) {
    size_t class = 0;
    block_t *block = head[class];
    while (class < 13) {
        while (block == NULL && class < 12) {
            block = head[class + 1];
            class += 1;
        }
        if (block == NULL) {
            return true;
        }
        do {
            if ((long)block % 8 != 0) {
                dbg_printf(
                    "a block address not alignment occures in line....:%d\n",
                    line);
                return false;
            } else {
                block = block->node.next;
            }

        } while (block != head[class]);
        block = head[class + 1];
        class += 1;
    }
    return true;
}

/**@brief check whether there is allocated blocks in the segregated list
 * @param[in] line
 * @return a boolean whether there is allocated blocks in the segregated list
 */
bool check_allocated_block_in_free_list(int line) {
    size_t class = 0;
    block_t *block = head[class];
    while (class < 13) {
        while (block == NULL && class < 12) {
            block = head[class + 1];
            class += 1;
        }
        if (block == NULL) {
            return true;
        }
        do {

            if (get_alloc(block) == true) {
                dbg_printf("allocated block in free list:%d\n", line);
                return false;
            } else {
                block = block->node.next;
            }

        } while (block != head[class]);
        block = head[class + 1];
        class += 1;
    }
    return true;
}

/**brief@check whether there are consecutive free blocks in the heap.
 * @param[in] line
 * @return a boolean whether there are consecutive free blocks in the heap
 */
bool check_consecutive_free_block(int line) {
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        bool current_alloc = true;
        bool next_alloc = true;
        if (block != NULL) {
            current_alloc = get_alloc(block);
        }

        block_t *next_block = find_next(block);
        if (next_block != NULL) {
            next_alloc = get_alloc(next_block);
        }
        if ((!current_alloc) && (!next_alloc)) {
            printf("Two consecutive unallocated block:%d\n", line);
            return false;
        }
    }
    return true;
}

/**@brief check whether payload is 16 bytes aligned
 * @param[in] line
 * @return a boolean whether payload is 16 bytes aligned
 */
bool payload_16bytes_aligned(int line) {
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        bool alloc = false;
        size_t size = 0;
        if (block != NULL) {
            alloc = get_alloc(block);
        }
        if (alloc) {
            size = get_size(block);
            if (size % 16 != 0) {
                dbg_printf("payload is not 16 bytes aligned:%d\n", line);
                return false;
            }
        }
    }
    return true;
}

/*heap checker, check the listed methods
 * @param[in] line
 * @return a boolean
 * */
bool mm_checkheap(int line) {
    prev_min_bit(line);
    payload_16bytes_aligned(line);
    check_pointer_alignment(line);
    check_consecutive_free_block(line);
    check_allocated_block_in_free_list(line);
    check_segregated_list_size_bound(line);
    return true;
}

/**
 * @brief initialize the heap and setting the heap's prologue and epilogue
 * @param[in] void
 * @return a boolean value indicate whether the heap has benn initializde.
 */
bool mm_init(void) {
    dbg_printf("call mm_init\n");
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, false, true, true); // Heap prologue (block footer)
    start[1] = pack(0, false, true, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    for (int i = 0; i < 15; i++) {
        head[i] = NULL;
    }

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief when a block is allocated, change its alloc status from unallocated to
 * allocated. At the same time, update next block's prev_alloc status
 * @param[in] size
 * @return void
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // adjust block size to include overhead and to meet alignment requirements
    asize = max(min_block_size, round_up(size + wsize, dsize));

    // search the free list for a fit
    block = find_fit(asize);

    // if no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // the block should be marked as free
    dbg_assert(!get_alloc(block));

    // mark block as allocated
    size_t block_size = get_size(block);
    bool prev_min = get_min_alloc(block);

    write_block(block, block_size, prev_min, true, true);

    delete (block);

    // try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief when an allocated block is freed, change its alloc status from
 * allocated to unallocated. At the same time, update next block's prev_alloc
 * status
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    /*find previous alloc status and size*/
    bool previous_alloc = true;
    block_t *previous_block = NULL;
    bool prev_min = get_min_alloc(block);

    if (block != NULL) {
        previous_alloc = get_prev_alloc(block);
        if (previous_alloc == false) {
            if (prev_min == true) {
                previous_block = (block_t *)((char *)block - min_block_size);

            } else {
                previous_block = find_prev(block);
            }
        }
    }

    // update block's status

    if (previous_alloc == false) {
        delete (previous_block); // delete previous block and then coalesce
        write_block(block, size, prev_min, false, false);

    } else if (previous_alloc == true) {
        write_block(block, size, prev_min, true, false);
    }

    // find next block's alloc status and size
    block_t *next_block = find_next(block);
    bool next_prev_min = get_min_alloc(next_block);
    bool next_alloc = true;
    size_t next_size = 0;

    // update next block's status
    if (next_block != NULL) {
        next_alloc = get_alloc(next_block);
        next_size = get_size(next_block);
        if (next_size != 0) {
            write_block(next_block, next_size, next_prev_min, false,
                        next_alloc);
        }

        // if nor block is unallocted, delete it from the free list
        if (next_alloc == false) {
            delete (next_block);
        }
    }

    // try to coalesce the block with its neighbors
    block = coalesce_block(block);
    insert(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief resize the memory block pointed to by ptr that is previously allocated
 * with a call to malloc or calloc
 * @param[in] ptr
 * @param[in] size
 * @return a pointer to the newly allocated memory or NULL if the request fails
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief allocates a block of memeory for an array with elements value, each of
 * them size bytes long and intitializes all its bits to zero
 * @param[in] elements
 * @param[in] size
 * @return void
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
