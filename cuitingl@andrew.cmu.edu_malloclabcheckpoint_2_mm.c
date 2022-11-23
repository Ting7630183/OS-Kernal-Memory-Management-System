/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
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
static const size_t min_block_size = 2 * dsize;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 */
static const word_t alloc_mask = 0x1;

/**
 * TODO: explain what size_mask is
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block block_t;
struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;
    union {
        struct {
            block_t *previous;
            block_t *next;
        };
        char payload[0];
    } node;
};

/**
 * @brief A pointer to the block payload.
 *
 * TODO: feel free to delete this comment once you've read it carefully.
 * We don't know what the size of the payload will be, so we will declare
 * it as a zero-length array, which is a GCC compiler extension. This will
 * allow us to obtain a pointer to the start of the payload.
 *
 * WARNING: A zero-length array must be the last element in a struct, so
 * there should not be any struct fields after it. For this lab, we will
 * allow you to include a zero-length array in a union, as long as the
 * union is the last field in its containing struct. However, this is
 * compiler-specific behavior and should be avoided in general.
 *
 * WARNING: DO NOT cast this pointer to/from other types! Instead, you
 * should use a union to alias this zero-length array with another struct,
 * in order to store additional types of data in the payload memory.
 */
/*char payload[0]; */

/*
 * TODO: delete or replace this comment once you've thought about it.
 * Why can't we declare the block footer here as part of the struct?
 * Why do we even have footers -- will the code work fine without them?
 * which functions actually use the data contained in footers?
 */

/* Global variables */
block_t *head[12];

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
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
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
    return asize - dsize;
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
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
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
    block->header = pack(0, true);
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
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc);
    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, alloc);
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

/*get the class of the specific segregated list.*/
size_t get_class(size_t size) {
    if (size < (min_block_size * 2)) {
        return 0;
    } else if (size < (min_block_size * 4)) {
        return 1;
    } else if (size < (min_block_size * 8)) {
        return 2;
    } else if (size < (min_block_size * 16)) {
        return 3;
    } else if (size < (min_block_size * 32)) {
        return 4;
    } else if (size < (min_block_size * 64)) {
        return 5;
    } else if (size < (min_block_size * 128)) {
        return 6;
    } else if (size < (min_block_size * 256)) {
        return 7;
    } else if (size < (min_block_size * 512)) {
        return 8;
    } else if (size < (min_block_size * 1024)) {
        return 9;
    } else if (size < (min_block_size * 2048)) {
        return 10;
    } else {
        return 11;
    }
    return 0;
}

/*insert a block in the free list.*/
void insert(block_t *block) {
    if (block == NULL) {
        return;
    }
    size_t block_size = get_size(block);
    size_t class = get_class(block_size);
    dbg_printf("insert at address:%p\n", block);
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

/*delete a block in the free list*/
void delete (block_t *block) {
    dbg_printf("delete at address:%p\n", block);
    if (block == NULL) {
        return;
    }
    size_t block_size = get_size(block);
    size_t class = get_class(block_size);
    if (block->node.next == block) {
        head[class] = NULL;
        return;
    } else {
        if (block->node.next != NULL) {
            if (block->node.previous != NULL) {
                block->node.next->node.previous = block->node.previous;
                block->node.previous->node.next = block->node.next;
                if (block == head[class]) {
                    head[class] = block->node.next;
                }
            }
        }
    }
}

/*coalesce block with previous and next block, return the pointer of the
 * coalesced block.*/
static block_t *coalesce_block(block_t *block) {

    if (block == NULL) {
        return NULL;
    }
    bool previous_alloc = true;
    bool next_alloc = true;
    size_t current_block_size = 0;
    size_t previous_size = 0;
    size_t next_size = 0;

    /*find previous and next block and their alloc status and size.*/
    block_t *previous_block = find_prev(block);
    block_t *next_block = find_next(block);

    /*find previous block's alloc status and size*/
    if (previous_block != NULL) {
        previous_alloc = get_alloc(previous_block);
        previous_size = get_size(previous_block);
    }
    /*find next block's alloc status and size*/
    if (next_block != NULL) {
        next_alloc = get_alloc(next_block);
        next_size = get_size(next_block);
    }

    /*find current block's size*/
    if (block != NULL) {
        current_block_size = get_size(block);
    }

    /*if both previous block and next block are allocated,return current block*/
    if (previous_alloc && next_alloc) {
        dbg_printf("coalesce case 1\n");
        return block;
    }

    /*if previous block is not allocated and next block is allocated, combine
     * previous block and current block*/
    if ((!previous_alloc) && next_alloc) {
        if (previous_block != NULL) {
            dbg_printf("coalesce case 2\n");
            size_t total_size = current_block_size + previous_size;
            write_block(previous_block, total_size, false);
            return previous_block;
        }
    }

    /*if previous block is allocated and next block is not allocated, combine
     * current block and next block*/
    if (previous_alloc && (!next_alloc)) {
        dbg_printf("coalesce case 3\n");
        size_t total_size = current_block_size + next_size;
        write_block(block, total_size, false);
        return block;
    }

    /*if both previous and next block are not allocated, combine three blocks
     * together*/
    if ((!previous_alloc) && (!next_alloc)) {
        dbg_printf("coalesce case 4\n");
        if (previous_block != NULL) {
            size_t total_size = current_block_size + previous_size + next_size;
            write_block(previous_block, total_size, false);
            return previous_block;
        }
    }

    return block;
}

/*
 * TODO: delete or replace this comment once you're done.
 *
 * Before you start, it will be helpful to review the "Dynamic Memory
 * Allocation: Basic" lecture, and especially the four coalescing
 * cases that are described.
 *
 * The actual content of the function will probably involve a call to
 * find_prev(), and multiple calls to write_block(). For examples of how
 * to use write_block(), take a look at split_block().
 *
 * Please do not reference code from prior semesters for this, including
 * old versions of the 213 website. We also discourage you from looking
 * at the malloc code in CS:APP and K&R, which make heavy use of macros
 * and which we no longer consider to be good style.
 */

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    dbg_printf("call extend_heap\n");
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about what bp represents. Why do we write the new block
     * starting one word BEFORE bp, but with the same size that we
     * originally requested?
     */

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    /*check whether previous block is free, if so delete it from free list*/
    block_t *previous_block = find_prev(block);
    if (previous_block != NULL) {
        bool previous_alloc = get_alloc(previous_block);
        if (previous_alloc == false) {
            delete (previous_block);
        }
    }
    /*coalesce in cae the previous block was free.*/
    block = coalesce_block(block);
    insert(block);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_printf("call split_block at address:%p\n", block);
    dbg_requires(get_alloc(block));
    /*if block size minus asize is larger than minimal size, split it */

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true);

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false);
        insert(block_next);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    size_t class = get_class(asize);
    block_t *block = head[class];

    while (class < 12) {
        while (block == NULL && class < 11) {
            block = head[class + 1];
            class += 1;
        }
        if (block == NULL) {
            return NULL;
        }
        do {

            if (!(get_alloc(block)) && (asize <= get_size(block))) {
                return block;
            } else {
                block = block->node.next;
            }

        } while (block != head[class]);
        block = head[class + 1];
        class += 1;
    }
    return NULL;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] line
 * @return
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

/*check prev/next pointer in the segregated list are consistent*/
bool check_segregated_list_pointer_consistency(int line) {
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
            block_t *next = block->node.next;
            if (block != next->node.previous) {
                dbg_printf("prev/next inconsistency:%d\n", line);
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

/*check iwhether there is allocated blocks in the segregated list*/
bool check_allocated_block_in_free_list(int line) {
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

/*check whether there are consecutive free blocks in the heap.*/
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

/*check whether payload is 16 bytes aligned*/
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

/*heap checker*/
bool mm_checkheap(int line) {
    payload_16bytes_aligned(line);
    check_segregated_list_pointer_consistency(line);
    check_consecutive_free_block(line);
    check_allocated_block_in_free_list(line);
    check_segregated_list_size_bound(line);
    return true;
}
/*
 * TODO: Delete this comment!
 *
 * You will need to write the heap checker yourself.
 * Please keep modularity in mind when you're writing the heap checker!
 *
 * As a filler: one guacamole is equal to 6.02214086 x 10**23 guacas.
 * One might even call it...  the avocado's number.
 *
 * Internal use only: If you mix guacamole on your bibimbap,
 * do you eat it with a pair of chopsticks, or with a spoon?
 */

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about why we need a heap prologue and epilogue. Why do
     * they correspond to a block footer and header respectively?
     */

    start[0] = pack(0, true); // Heap prologue (block footer)
    start[1] = pack(0, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    head[0] = NULL;
    head[1] = NULL;
    head[2] = NULL;
    head[3] = NULL;
    head[4] = NULL;
    head[5] = NULL;
    head[6] = NULL;
    head[7] = NULL;
    head[8] = NULL;
    head[9] = NULL;
    head[10] = NULL;
    head[11] = NULL;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
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

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);
    dbg_printf("use malloc size:%lu\n", asize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true);
    dbg_printf("malloc at address:%p\n", block);
    delete (block);

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    dbg_printf("call free at address:%p\n", block);

    /*find the previous and next block.*/
    block_t *previous_block = find_prev(block);
    block_t *next_block = find_next(block);
    bool previous_alloc = true;
    bool next_alloc = true;

    /*if previous block is free, delete it in the free list.*/
    if (previous_block != NULL) {
        previous_alloc = get_alloc(previous_block);
        if (previous_alloc == false) {
            dbg_printf(
                "delete previous block at the address before coalesce:%p\n",
                previous_block);
            delete (previous_block);
        }
    }

    /*if next block is free, delete it in the free list.*/
    if (next_block != NULL) {
        next_alloc = get_alloc(next_block);
        if (next_alloc == false) {
            dbg_printf("delete next block at the address before coalecse:%p\n",
                       block);
            delete (next_block);
        }
    }

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);
    insert(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
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
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
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
