/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*                  Benedikt Meurer, University of Siegen              */
/*                                                                     */
/*    Copyright 1998 Institut National de Recherche en Informatique    */
/*    et en Automatique. Copyright 2012 Benedikt Meurer. All rights    */
/*    reserved. This file is distributed under the terms of the GNU    */
/*    Library General Public License, with the special exception on    */
/*    linking described in file ../LICENSE.                            */
/*                                                                     */
/***********************************************************************/

/* $Id$ */

/* Asm part of the runtime system, ARM processor */
/* Must be preprocessed by cpp */

        .syntax unified
        .text
#if defined(SYS_linux_eabihf)
        .arch   armv7-a
        .fpu    vfpv3-d16
        .thumb
#elif defined(SYS_linux_eabi)
        .arch   armv4t
        .arm

    /* Compatibility macros */
        .macro  blx reg
        mov     lr, pc
        bx      \reg
        .endm
        .macro  cbz reg, lbl
        cmp     \reg, #0
        beq     \lbl
        .endm
        .macro  vpop regs
        .endm
        .macro  vpush regs
        .endm
#elif defined(SYS_macosx)
        .machine armv6
        .arm

    /* Compatibility macros */
        .macro  cbz reg, lbl
        cmp     \reg, #0
        beq     \lbl
        .endm
        .macro  .size
        .endm
        .macro  .type
        .endm
#endif

#if defined(SYS_linux_eabi) || defined(SYS_linux_eabihf)
#define G(x) x
#define L(x) .L##x
#else
#define G(x) _##x
#define L(x) L##x
#endif

trap_ptr        .req    r8
alloc_ptr       .req    r10
alloc_limit     .req    r11

/* Support for profiling with gprof */

#if defined(PROFILING) && (defined(SYS_linux_eabi) || defined(SYS_linux_eabihf))
#define PROFILE \
        push    {lr}; \
        bl      G(__gnu_mcount_nc)
#else
#define PROFILE
#endif

/* Allocation functions and GC interface */

        .globl  G(caml_system__code_begin)
G(caml_system__code_begin):

        .align  2
        .globl  G(caml_call_gc)
G(caml_call_gc):
        PROFILE
    /* Record return address */
        ldr     r12, L(caml_last_return_address)
        str     lr, [r12]
L(caml_call_gc):
    /* Record lowest stack address */
        ldr     r12, L(caml_bottom_of_stack)
        str     sp, [r12]
    /* Save caller floating-point registers on the stack */
        vpush   {d0-d7}
    /* Save integer registers and return address on the stack */
        push    {r0-r7,r12,lr}
    /* Store pointer to saved integer registers in caml_gc_regs */
        ldr     r12, L(caml_gc_regs)
        str     sp, [r12]
    /* Save current allocation pointer for debugging purposes */
        ldr     alloc_limit, L(caml_young_ptr)
        str     alloc_ptr, [alloc_limit]
    /* Save trap pointer in case an exception is raised during GC */
        ldr     r12, L(caml_exception_pointer)
        str     trap_ptr, [r12]
    /* Call the garbage collector */
        bl      G(caml_garbage_collection)
    /* Restore integer registers and return address from the stack */
        pop     {r0-r7,r12,lr}
    /* Restore floating-point registers from the stack */
        vpop    {d0-d7}
    /* Reload new allocation pointer and limit */
    /* alloc_limit still points to caml_young_ptr */
        ldr     r12, L(caml_young_limit)
        ldr     alloc_ptr, [alloc_limit]
        ldr     alloc_limit, [r12]
    /* Return to caller */
        bx      lr
        .type   G(caml_call_gc), %function
        .size   G(caml_call_gc), .-G(caml_call_gc)

        .align  2
        .globl  G(caml_alloc1)
G(caml_alloc1):
        PROFILE
L(caml_alloc1):
        sub     alloc_ptr, alloc_ptr, 8
        cmp     alloc_ptr, alloc_limit
        bcc     1f
        bx      lr
1:  /* Record return address */
        ldr     r7, L(caml_last_return_address)
        str     lr, [r7]
    /* Call GC (preserves r7) */
        bl      L(caml_call_gc)
    /* Restore return address */
        ldr     lr, [r7]
    /* Try again */
        b       L(caml_alloc1)
        .type   G(caml_alloc1), %function
        .size   G(caml_alloc1), .-G(caml_alloc1)

        .align  2
        .globl  G(caml_alloc2)
G(caml_alloc2):
        PROFILE
L(caml_alloc2):
        sub     alloc_ptr, alloc_ptr, 12
        cmp     alloc_ptr, alloc_limit
        bcc     1f
        bx      lr
1:  /* Record return address */
        ldr     r7, L(caml_last_return_address)
        str     lr, [r7]
    /* Call GC (preserves r7) */
        bl      L(caml_call_gc)
    /* Restore return address */
        ldr     lr, [r7]
    /* Try again */
        b       L(caml_alloc2)
        .type   G(caml_alloc2), %function
        .size   G(caml_alloc2), .-G(caml_alloc2)

        .align  2
        .globl  G(caml_alloc3)
G(caml_alloc3):
        PROFILE
L(caml_alloc3):
        sub     alloc_ptr, alloc_ptr, 16
        cmp     alloc_ptr, alloc_limit
        bcc     1f
        bx      lr
1:  /* Record return address */
        ldr     r7, L(caml_last_return_address)
        str     lr, [r7]
    /* Call GC (preserves r7) */
        bl      L(caml_call_gc)
    /* Restore return address */
        ldr     lr, [r7]
    /* Try again */
        b       L(caml_alloc3)
        .type   G(caml_alloc3), %function
        .size   G(caml_alloc3), .-G(caml_alloc3)

        .align  2
        .globl  G(caml_allocN)
G(caml_allocN):
        PROFILE
L(caml_allocN):
        sub     alloc_ptr, alloc_ptr, r7
        cmp     alloc_ptr, alloc_limit
        bcc     1f
        bx      lr
1:  /* Record return address */
        ldr     r12, L(caml_last_return_address)
        str     lr, [r12]
    /* Call GC (preserves r7) */
        bl      L(caml_call_gc)
    /* Restore return address */
        ldr     r12, L(caml_last_return_address)
        ldr     lr, [r12]
    /* Try again */
        b       L(caml_allocN)
        .type   G(caml_allocN), %function
        .size   G(caml_allocN), .-G(caml_allocN)

/* Call a C function from OCaml */
/* Function to call is in r7 */

        .align  2
        .globl  G(caml_c_call)
G(caml_c_call):
        PROFILE
    /* Record lowest stack address and return address */
        ldr     r5, L(caml_last_return_address)
        ldr     r6, L(caml_bottom_of_stack)
        str     lr, [r5]
        str     sp, [r6]
    /* Preserve return address in callee-save register r4 */
        mov     r4, lr
    /* Make the exception handler alloc ptr available to the C code */
        ldr     r5, L(caml_young_ptr)
        ldr     r6, L(caml_exception_pointer)
        str     alloc_ptr, [r5]
        str     trap_ptr, [r6]
    /* Call the function */
        blx     r7
    /* Reload alloc ptr and alloc limit */
        ldr     r6, L(caml_young_limit)
        ldr     alloc_ptr, [r5]         /* r5 still points to caml_young_ptr */
        ldr     alloc_limit, [r6]
    /* Return */
        bx      r4
        .type   G(caml_c_call), %function
        .size   G(caml_c_call), .-G(caml_c_call)

/* Start the OCaml program */

        .align  2
        .globl  G(caml_start_program)
G(caml_start_program):
        PROFILE
        ldr     r12, L(caml_program)

/* Code shared with caml_callback* */
/* Address of OCaml code to call is in r12 */
/* Arguments to the OCaml code are in r0...r3 */

L(jump_to_caml):
    /* Save return address and callee-save registers */
        vpush   {d8-d15}
        push    {r4-r8,r10,r11,lr}              /* 8-byte alignment */
    /* Setup a callback link on the stack */
        sub     sp, sp, 4*4                     /* 8-byte alignment */
        ldr     r4, L(caml_bottom_of_stack)
        ldr     r5, L(caml_last_return_address)
        ldr     r6, L(caml_gc_regs)
        ldr     r4, [r4]
        ldr     r5, [r5]
        ldr     r6, [r6]
        str     r4, [sp, 0]
        str     r5, [sp, 4]
        str     r6, [sp, 8]
    /* Setup a trap frame to catch exceptions escaping the OCaml code */
        sub     sp, sp, 2*4
        ldr     r6, L(caml_exception_pointer)
        ldr     r5, L(Ltrap_handler)
        ldr     r4, [r6]
        str     r4, [sp, 0]
        str     r5, [sp, 4]
        mov     trap_ptr, sp
    /* Reload allocation pointers */
        ldr     r4, L(caml_young_ptr)
        ldr     alloc_ptr, [r4]
        ldr     r4, L(caml_young_limit)
        ldr     alloc_limit, [r4]
    /* Call the OCaml code */
        blx     r12
L(caml_retaddr):
    /* Pop the trap frame, restoring caml_exception_pointer */
        ldr     r4, L(caml_exception_pointer)
        ldr     r5, [sp, 0]
        str     r5, [r4]
        add     sp, sp, 2*4
    /* Pop the callback link, restoring the global variables */
L(return_result):
        ldr     r4, L(caml_bottom_of_stack)
        ldr     r5, [sp, 0]
        str     r5, [r4]
        ldr     r4, L(caml_last_return_address)
        ldr     r5, [sp, 4]
        str     r5, [r4]
        ldr     r4, L(caml_gc_regs)
        ldr     r5, [sp, 8]
        str     r5, [r4]
        add     sp, sp, 4*4
    /* Update allocation pointer */
        ldr     r4, L(caml_young_ptr)
        str     alloc_ptr, [r4]
    /* Reload callee-save registers and return */
        pop     {r4-r8,r10,r11,lr}
        vpop    {d8-d15}
        bx      lr
        .type   L(caml_retaddr), %function
        .size   L(caml_retaddr), .-L(caml_retaddr)
        .type   G(caml_start_program), %function
        .size   G(caml_start_program), .-G(caml_start_program)

/* The trap handler */

        .align  2
L(trap_handler):
    /* Save exception pointer */
        ldr     r12, L(caml_exception_pointer)
        str     trap_ptr, [r12]
    /* Encode exception bucket as an exception result */
        orr     r0, r0, 2
    /* Return it */
        b       L(return_result)
        .type   L(trap_handler), %function
        .size   L(trap_handler), .-L(trap_handler)

/* Raise an exception from OCaml */

        .align  2
        .globl  G(caml_raise_exn)
G(caml_raise_exn):
        PROFILE
    /* Test if backtrace is active */
        ldr     r1, L(caml_backtrace_active)
        ldr     r1, [r1]
        cbz     r1, 1f
    /* Preserve exception bucket in callee-save register r4 */
        mov     r4, r0
    /* Stash the backtrace */
        mov     r1, lr                          /* arg2: pc of raise */
        mov     r2, sp                          /* arg3: sp of raise */
        mov     r3, trap_ptr                    /* arg4: sp of handler */
        bl      G(caml_stash_backtrace)
    /* Restore exception bucket */
        mov     r0, r4
1:  /* Cut stack at current trap handler */
        mov     sp, trap_ptr
    /* Pop previous handler and addr of trap, and jump to it */
        pop     {trap_ptr, pc}
        .type   G(caml_raise_exn), %function
        .size   G(caml_raise_exn), .-G(caml_raise_exn)

/* Raise an exception from C */

        .align  2
        .globl  G(caml_raise_exception)
G(caml_raise_exception):
        PROFILE
    /* Reload trap ptr, alloc ptr and alloc limit */
        ldr     trap_ptr, L(caml_exception_pointer)
        ldr     alloc_ptr, L(caml_young_ptr)
        ldr     alloc_limit, L(caml_young_limit)
        ldr     trap_ptr, [trap_ptr]
        ldr     alloc_ptr, [alloc_ptr]
        ldr     alloc_limit, [alloc_limit]
    /* Test if backtrace is active */
        ldr     r1, L(caml_backtrace_active)
        ldr     r1, [r1]
        cbz     r1, 1f
    /* Preserve exception bucket in callee-save register r4 */
        mov     r4, r0
        ldr     r1, L(caml_last_return_address)
        ldr     r1, [r1]                        /* arg2: pc of raise */
        ldr     r2, L(caml_bottom_of_stack)
        ldr     r2, [r2]                        /* arg3: sp of raise */
        mov     r3, trap_ptr                    /* arg4: sp of handler */
        bl      G(caml_stash_backtrace)
    /* Restore exception bucket */
        mov     r0, r4
1:  /* Cut stack at current trap handler */
        mov     sp, trap_ptr
    /* Pop previous handler and addr of trap, and jump to it */
        pop     {trap_ptr, pc}
        .type   G(caml_raise_exception), %function
        .size   G(caml_raise_exception), .-G(caml_raise_exception)

/* Callback from C to OCaml */

        .align  2
        .globl  G(caml_callback_exn)
G(caml_callback_exn):
        PROFILE
    /* Initial shuffling of arguments (r0 = closure, r1 = first arg) */
        mov     r12, r0
        mov     r0, r1          /* r0 = first arg */
        mov     r1, r12         /* r1 = closure environment */
        ldr     r12, [r12]      /* code pointer */
        b       L(jump_to_caml)
        .type   G(caml_callback_exn), %function
        .size   G(caml_callback_exn), .-G(caml_callback_exn)

        .align  2
        .globl  G(caml_callback2_exn)
G(caml_callback2_exn):
        PROFILE
    /* Initial shuffling of arguments (r0 = closure, r1 = arg1, r2 = arg2) */
        mov     r12, r0
        mov     r0, r1          /* r0 = first arg */
        mov     r1, r2          /* r1 = second arg */
        mov     r2, r12         /* r2 = closure environment */
        ldr     r12, L(caml_apply2)
        b       L(jump_to_caml)
        .type   G(caml_callback2_exn), %function
        .size   G(caml_callback2_exn), .-G(caml_callback2_exn)

        .align  2
        .globl  G(caml_callback3_exn)
G(caml_callback3_exn):
        PROFILE
    /* Initial shuffling of arguments */
    /* (r0 = closure, r1 = arg1, r2 = arg2, r3 = arg3) */
        mov     r12, r0
        mov     r0, r1          /* r0 = first arg */
        mov     r1, r2          /* r1 = second arg */
        mov     r2, r3          /* r2 = third arg */
        mov     r3, r12         /* r3 = closure environment */
        ldr     r12, L(caml_apply3)
        b       L(jump_to_caml)
        .type   G(caml_callback3_exn), %function
        .size   G(caml_callback3_exn), .-G(caml_callback3_exn)

        .align  2
        .globl  G(caml_ml_array_bound_error)
G(caml_ml_array_bound_error):
        PROFILE
    /* Load address of [caml_array_bound_error] in r7 */
        ldr     r7, L(caml_array_bound_error)
    /* Call that function */
        b       G(caml_c_call)
        .type   G(caml_ml_array_bound_error), %function
        .size   G(caml_ml_array_bound_error), .-G(caml_ml_array_bound_error)

/* Global references */

L(caml_apply2):               .word G(caml_apply2)
L(caml_apply3):               .word G(caml_apply3)
L(caml_array_bound_error):    .word G(caml_array_bound_error)
L(caml_backtrace_active):     .word G(caml_backtrace_active)
L(caml_bottom_of_stack):      .word G(caml_bottom_of_stack)
L(caml_exception_pointer):    .word G(caml_exception_pointer)
L(caml_gc_regs):              .word G(caml_gc_regs)
L(caml_last_return_address):  .word G(caml_last_return_address)
L(caml_program):              .word G(caml_program)
L(caml_young_limit):          .word G(caml_young_limit)
L(caml_young_ptr):            .word G(caml_young_ptr)
L(Ltrap_handler):             .word L(trap_handler)

        .globl  G(caml_system__code_end)
G(caml_system__code_end):

/* GC roots for callback */

        .data
        .align  2
        .globl  G(caml_system__frametable)
G(caml_system__frametable):
        .word   1               /* one descriptor */
        .word   L(caml_retaddr) /* return address into callback */
        .short  -1              /* negative frame size => use callback link */
        .short  0               /* no roots */
        .align  2
        .type   G(caml_system__frametable), %object
        .size   G(caml_system__frametable), .-G(caml_system__frametable)
