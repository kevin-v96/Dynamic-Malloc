/* 
 * Simple, 32-bit and 64-bit clean allocator based on an explicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are chk_align to double-word boundaries.  This
 * yields 8-byte chk_align blocks on a 32-bit processor, and 16-byte chk_align
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"S.W.A.T Cats",
	/* First member's full name */
	"Kevin Vegda",
	/* First member's email id*/
	"201401014@daiict.ac.in",
	/* Second member's full name */
	"Rudra Chandak",
	/* Second member's email id */
	"201401129@daiict.ac.in"
};


/* Basic constants and macros */
#define WSIZE 4       /* Word and header/footer size (bytes) */ 
#define DSIZE 8       /* Doubleword size (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at pointer p */
#define GET(p)       (*(unsigned int *)(p))           
#define PUT(p, val)  (*(unsigned int *)(p) = (val)) 

/* Read the size and allocated fields from pointer p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                  
#define GET_ALLOC(p) (GET(p) & 0x1)             

/* Given block ptr bp, compute pointer of its header and footer */
#define HDRP(bp) (bp - WSIZE)
#define FTRP(bp) (bp + GET_SIZE(HDRP(bp)))

/* Given block ptr bp, compute pointer of next and previous blocks */
#define NEXT_BLKP(bp) ((bp) + GET_SIZE(HDRP(bp)) + 2*WSIZE)
#define PREV_BLKP(bp) (bp - GET_SIZE(bp-DSIZE) - 2*WSIZE)

/* Setters and getters for the linked list*/
#define GET_NXT(bp)   (*(void **)(bp + DSIZE))
#define GET_PRV(bp)   (*(void **)bp)
#define SET_NXT(bp, ptr)  (GET_NXT(bp) = ptr)
#define SET_PRV(bp, ptr)  (GET_PRV(bp) = ptr)

/*Calculates the actual size with alignment requirements satisfied*/
#define CALC_ALIGN(p) (((size_t)(p) + (7)) & ~(0x7))

/* Global variables: */
void* freel_head;  /* Head of free list */
static char *heap_listp; /* Pointer to first block */  

/* Function prototypes for internal helper routines*/
static void coalesce(void *ptr);

/*User-implemented routines*/
static void *split_n_place(void *ptr, size_t newsize);
static void freel_insert(void *ptr);
static void freel_remove(void *ptr);
static void *extend_heap(size_t asize);
static void *find_fit(void *freel_ptr,size_t asize);

/*Heap consistency checks*/
static int check_in_heap(const void *p);
static void printblock(void *bp); 
static void checkblock(void *bp);
void checkheap(bool verbose);
static int is_free();
static int not_coalesced();
static int in_free_list();
static int overlap();
static int valid();

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
	int 
mm_init(void) 
{
	void * heap_bottom = mem_heap_lo();				//Gets the start of the heap with the mem_heap_lo fuction of memlib.h
	freel_head = NULL;						//Initialize the free list

	if ((heap_bottom = extend_heap(0)) == (void *)-1)		//Extend the heap for the initial padding and prologue
	{
		return -1;
	}

	heap_listp = heap_bottom + (2 * WSIZE);			//Get address if heap_listp, from where we will start allocation
	PUT(heap_bottom, PACK(0,1));          			//The padding at the start
	PUT((char *)heap_bottom + WSIZE, PACK(0,1)); 			//The prologue header - The epilogue is allocated by extend_heap

	return 0;
}


/* 
 * Requires:
 *   None.
 *
 * Effects:
 *    Allocate using a explicit free list implementation.
 *     Use a first-fit policy to allocate a block of space, using splitting if necessary.
 *     Splitting a free block is done so that the free block precedes the allocated block.
 *     Allocate a new block if no suitable block is found, return NULL if out of memory
 */

	void 
*mm_malloc(size_t size) 
{   
	unsigned int asize;			
	void *freel_ptr = freel_head;				//Get a freelist pointer to go through the list

	if (size <= 0)					
	{
		return NULL;					//Invalid case
	}

	// Align the block properly
	if (size <= 4*DSIZE)
	{
		asize = 4*DSIZE;				
	}
	else
	{
		asize=CALC_ALIGN(size) + 128;
	}      

	// search free list for first free block for size newsize
	freel_ptr=find_fit(freel_ptr,asize);		
	return freel_ptr;
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */

	static void *
find_fit(void *freel_ptr,size_t asize)
{
	int i = 0;
	unsigned int tempsize = 0;

	while (freel_ptr != NULL && i < 300) 				//Pseudoo-first fit to find the needed block
	{
		tempsize = GET_SIZE(HDRP(freel_ptr));
		if (tempsize >= asize) 
		{
			if (tempsize >= asize + 32)
			{
				return split_n_place(freel_ptr, asize);
			}   

			freel_remove(freel_ptr);			//Remove the block from the free list

			PUT(HDRP(freel_ptr), PACK(tempsize, 1));	//Allocate the free block
			PUT(FTRP(freel_ptr), PACK(tempsize, 1));
			return freel_ptr;
		}
		else 
		{
			freel_ptr = GET_NXT(freel_ptr); 
		}

		i++;
	}

	freel_ptr = extend_heap(asize);				//If a fit is not found, extend the heap by the required amount

	// return NULL if out of memory  
	if ((long)freel_ptr == -1)
	{
		return NULL;
	}

	// else allocate memory and update epilogue
	PUT(HDRP(freel_ptr), PACK(asize, 1));
	PUT(FTRP(freel_ptr), PACK(asize, 1));
	PUT(FTRP(freel_ptr) + WSIZE, PACK(0, 1));			//Update epilogue

	return freel_ptr;
}


/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with size 'asize' and return that block's address.
 */
	static void *
extend_heap(size_t asize) 
{
	void *p;
	p=mem_sbrk(asize + 2*WSIZE);		//Extend the heap by the required amount (asize)+ the space required for the header and footer
	return p;
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 * Freeing a block.
 * freel_insert to free list if necessary.
 * Coalesce if there are blocks in the free list
 */

	void 
mm_free(void *bp)
{

	size_t size = GET_SIZE(HDRP(bp)); 

	if(bp == 0)
	{
		return;	
	}

	PUT(HDRP(bp), PACK(size, 0));		//Free the block 
	PUT(FTRP(bp), PACK(size, 0));

	if(freel_head != NULL)
	{
		coalesce(bp);
	} 
	else
	{
		freel_insert(bp);		//Insert block in the free list
	}
}


/*
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "bp" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "bp" and returns NULL.  If the block "bp" is already a block with at
 *   least "size" bytes of payload, then "bp" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "bp" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */


	void 
*mm_realloc(void *bp, size_t size) 
{
	size_t oldsize,temp;
	void *newptr;

	oldsize=GET_SIZE(HDRP(bp));
	// If size is 0 
	if (size == 0) 
	{
		mm_free(bp);			//If the required size is zero, this request is basically a call to mm_free
		return 0;
	}

	if(size<=oldsize)
	{
		newptr=bp;
		return newptr;
	}

	else
	{

		// If oldptr is NULL, then this is just malloc
		if (bp == NULL) 
		{
			return mm_malloc(size);
		}
		temp=CALC_ALIGN(size);


		if(GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0 && temp-oldsize <= GET_SIZE(HDRP(NEXT_BLKP(bp))))	//If the next block is free
		{												//and has enough space to 
			temp= GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(bp)) +8;				//accomodate the difference
			freel_remove(NEXT_BLKP(bp));								//between the new size and
			//old size, coalesce.

			PUT(HDRP(bp), PACK(temp, 1));
			PUT(FTRP(bp), PACK(temp, 1));

			newptr=bp;
			return newptr;
		}

		else
		{   
			newptr = mm_malloc(size);			//Else, allocate more space
			if (!newptr) 
			{
				return 0;
			}

			oldsize = GET_SIZE(HDRP(bp));		//Get the old size

			if (size < oldsize) 
				oldsize = size; //If the new size is less than the old one, cut short the block by the required amount  

			memcpy(newptr, bp, oldsize);
			mm_free(bp);		//Free the block

			return newptr;
		}
	}
}

/*  
 * Requires:
 *   "ptr" is the address of a newly freed block.
 *
 * Effects:
 * Done to minimize internal fragmentation.
 * Four Cases:
 * 1. Nearby blocks are both allocated. Simply freel_insert pointer of current block. No coalescing done.
 * 2. Previous block is allocated, next block is free. Update size of current block, freel_remove the ptr of next block,
 *    and then freel_insert ptr of newly sized block to the list.
 * 3. Next block is allocated, previous is free. Update size of previous block.
 * 4. Nearby blocks are both free. Update size of previous block, freel_remove ptr of next block.
 */
	static void 
coalesce(void *ptr) 
{
	size_t next_alloc_status = GET_ALLOC((char *)(FTRP(ptr)) + WSIZE);
	size_t prev_alloc_status = GET_ALLOC((char *)(ptr) - DSIZE);
	size_t size = GET_SIZE(HDRP(ptr));

	// case 1 - Both allocated
	if (prev_alloc_status && next_alloc_status)
	{
		freel_insert(ptr);
	} 
	// case 2 - Previous free, next allocated
	else if (!prev_alloc_status && next_alloc_status)
	{
		ptr = PREV_BLKP(ptr);
		size += GET_SIZE(HDRP(ptr)) + 2*WSIZE;
		PUT(HDRP(ptr), PACK(size, 0));
		PUT(FTRP(ptr), PACK(size, 0));
	} 
	// case 3 - Previous allocated, next free
	else if (prev_alloc_status && !next_alloc_status) 
	{  
		size += GET_SIZE(HDRP(NEXT_BLKP(ptr))) + 2*WSIZE;
		freel_remove(NEXT_BLKP(ptr));
		PUT(HDRP(ptr), PACK(size, 0));
		PUT(FTRP(ptr), PACK(size, 0));
		freel_insert(ptr);
	} 
	// case 4 - Both previous and next free
	else { 
		void * prev = PREV_BLKP(ptr);
		void * next = NEXT_BLKP(ptr);   
		size += GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(next)) + 4*WSIZE;
		PUT(HDRP(prev), PACK(size, 0));
		PUT(FTRP(prev), PACK(size, 0)); 
		freel_remove(next);       
	}
}


/* freel_insert - insert the specific block ptr 
 *to the free list, making it the first element in the list 
 */
	static  void 
freel_insert(void *ptr) 
{
	void *head = freel_head;
	SET_NXT(ptr, head);
	SET_PRV(ptr, NULL);
	if (head != NULL)
		SET_PRV(head, ptr);
	freel_head = ptr;
}

/* 
 * freel_remove - remove specific block ptr from free list
 * If we are trying to remove the ptr that is at the front of the list, then 
 * update the front of the list to be the next block ptr.
 */
	static  void 
freel_remove(void *ptr)
{
	void *next = GET_NXT(ptr);
	void *prev = GET_PRV(ptr);

	// start of the list
	if (prev == NULL)
	{
		freel_head = next;
		if (next != NULL) 
		{
			SET_PRV(next, NULL);
		}
	} 
	else 
	{
		SET_NXT(prev, next);
		if (next != NULL)
		{
			SET_PRV(next, prev);
		}
	}
}


/*
 * split_n_place - splits block so that we are allocating minimally 
 * Helps so that we allocate only the appropriate block size.
 * Takes pointer to current block and the needed size.
 * Finds newsize for block, places that block into the heap, and returns the pointer. 
 */
	static void* 
split_n_place(void *ptr, size_t newsize) 
{
	int new_fsize = GET_SIZE(HDRP(ptr)) - newsize - 2*WSIZE;

	PUT(HDRP(ptr), PACK(new_fsize, 0));
	PUT(FTRP(ptr), PACK(new_fsize, 0));
	void *p = NEXT_BLKP(ptr);
	PUT(HDRP(p), PACK(newsize, 1));
	PUT(FTRP(p), PACK(newsize, 1));

	return p;
}


//-----------------------------------------------------------------------------------------------------------------------------------------------------

//HEAP CONSISTENCY CHECKS

/*Is every block in the free list marked as free?*/
	static int 
is_free()							//USER HEAP CONSISTENCY CHECK 1
{
	void * freel_ptr=freel_head;
	while(freel_ptr!=NULL)
	{
		if((GET_ALLOC(HDRP(freel_ptr))==1)||(GET_ALLOC(FTRP(freel_ptr))==1))
		{	
			return 1;
		}
		freel_ptr=GET_NXT(freel_ptr);
	}
	return 0;
}

/*Are there any contiguous free blocks that somehow escaped coalescing?*/
	static int 
not_coalesced()						//USER HEAP CONSISTENCY CHECK 2
{
	void *p=freel_head;
	while(p!=NULL)
	{
		if(GET_ALLOC(HDRP(NEXT_BLKP(p)))==0)
			return 1;
		p=GET_NXT(p);
	}
	return 0;
}

/*Is every free block actually in the free list?*/
	static int 
in_free_list()						//USER HEAP CONSISTENCY CHECK 3
{
	void *p=heap_listp;

	while(GET_SIZE(HDRP(p)) > 0)
	{
		if(GET_ALLOC(HDRP(p))==0)
		{
			if(GET_PRV(p)==NULL&&GET_NXT(p)==NULL)
				return 1; 
		}
		p=NEXT_BLKP(p);
	}
	return 0;
}

/*Do pointers in the free list point to valid free blocks*/
//No need to check this, as the free list already contains the whole blocks as a linked list, and not just pointers to them.

/*Do any allocated blocks overlap?*/
	static int 
overlap()							//USER HEAP CONSISTENCY CHECK 4
{
	void *p=heap_listp;
	while(GET_SIZE(HDRP(p)) > 0)
	{
		if((GET_ALLOC(HDRP(p))==1)&&(GET_ALLOC(HDRP(NEXT_BLKP(p)))==1))
		{
			if((int)FTRP(p)>=(int)HDRP(NEXT_BLKP(p)))
				return 1;
		}
		p=NEXT_BLKP(p);
	}
	return 0;
}

/*Do the pointers in a heap block point to valid heap addresses?*/
	static int 
valid()							//USER HEAP CONSISTENCY CHECK 5
{
	void *p=heap_listp;
	int flag=0;
	while(GET_SIZE(HDRP(p)) > 0)
	{
		flag=check_in_heap(p);
		if(flag==1)
			return 1;
		p=NEXT_BLKP(p);
	}
	return 0;
}

/* check_in_heap - checks if the pointer is in the heap 
 */
	static int 
check_in_heap(const void *p) 				//Check if the pointer p is in the heap
{
	return p <= mem_heap_hi() && p >= mem_heap_lo();
}

//-----------------------------------------------------------------------------------------------------------------------------------------------------

/*
 * Requires:
 *   "bp" is the pointer of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
	static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword chk_align\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
	void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
			!GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");

	if(is_free()==1)
	{
		printf("There is at least one block in the free list which is marked as Allocated");
	}
	if(not_coalesced()==1)
	{
		printf("There were blocks found which were not properly coalesced.");
	}
	if(in_free_list()==1)
	{
		printf("There is at least one free block which is not included in the free list");
	}
	if(overlap()==1)
	{
		printf("There is at least one allocated block in the heap that overlaps with another allocated block.");
	}
	if(valid()==1)
	{
		printf("There is at least one pointer int the heap which points to an address outside the heap.");
	}
}

/*
 * Requires:
 *   "bp" is the pointer of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
	static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) 
	{
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
			hsize, (halloc ? 'a' : 'f'), 
			fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
