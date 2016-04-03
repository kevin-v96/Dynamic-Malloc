# Dynamic-Malloc

Dynamic memory allocator implemented for my System Software course.

 Simple, 32-bit and 64-bit clean allocator based on an explicit free list,
 first fit placement, and boundary tag coalescing, as described in the
 CS:APP2e text.  Blocks are chk_align to double-word boundaries.  This
 yields 8-byte chk_align blocks on a 32-bit processor, and 16-byte chk_align
 blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 than necessary; the assignment only requires 8-byte alignment.  The
 minimum block size is four words.
 
 This allocator uses the size of a pointer, e.g., sizeof(void *), to
 define the size of a word.  This allocator also uses the standard
 type uintptr_t to define unsigned integers that are the same size
 as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 
