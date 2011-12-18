/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1998 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* $Id$ */

/* Asm part of the runtime system, ARM processor */

trap_ptr        .req    r11
alloc_ptr       .req    r8
alloc_limit     .req    r10

        .text

/* Allocation functions and GC interface */

        .globl caml_call_gc
caml_call_gc:
    /* Record return address and desired size */
    /* Can use alloc_limit as a temporary since it will be reloaded by
       invoke_gc */
        ldr     alloc_limit, =caml_last_return_address
        str     lr, [alloc_limit, #0]
        ldr     alloc_limit, =caml_requested_size
        str     r12, [alloc_limit, #0]
    /* Branch to shared GC code */
        bl      .Linvoke_gc
    /* Finish allocation */
        ldr     r12, =caml_requested_size
        ldr     r12, [r12, #0]
        sub     alloc_ptr, alloc_ptr, r12
        bx      lr
        .type   caml_call_gc, %function
        .size   caml_call_gc, .-caml_call_gc

        .globl caml_alloc1
caml_alloc1:
        sub     alloc_ptr, alloc_ptr, #8
        cmp     alloc_ptr, alloc_limit
        movcs   pc, lr                /* Return if alloc_ptr >= alloc_limit */
    /* Record return address */
        ldr     r12, =caml_last_return_address
        str     lr, [r12, #0]
    /* Invoke GC */
        bl      .Linvoke_gc
    /* Try again */
        b       caml_alloc1
        .type   caml_alloc1, %function
        .size   caml_alloc1, .-caml_alloc1

        .globl caml_alloc2
caml_alloc2:
        sub     alloc_ptr, alloc_ptr, #12
        cmp     alloc_ptr, alloc_limit
        movcs   pc, lr                /* Return if alloc_ptr >= alloc_limit */
    /* Record return address */
        ldr     r12, =caml_last_return_address
        str     lr, [r12, #0]
    /* Invoke GC */
        bl      .Linvoke_gc
    /* Try again */
        b       caml_alloc2
        .type   caml_alloc2, %function
        .size   caml_alloc2, .-caml_alloc2

        .globl caml_alloc3
caml_alloc3:
        sub     alloc_ptr, alloc_ptr, #16
        cmp     alloc_ptr, alloc_limit
        movcs   pc, lr                /* Return if alloc_ptr >= alloc_limit */
    /* Record return address */
        ldr     r12, =caml_last_return_address
        str     lr, [r12, #0]
    /* Invoke GC */
        bl      .Linvoke_gc
    /* Try again */
        b       caml_alloc3
        .type   caml_alloc3, %function
        .size   caml_alloc3, .-caml_alloc3

        .globl caml_allocN
caml_allocN:
        sub     alloc_ptr, alloc_ptr, r12
        cmp     alloc_ptr, alloc_limit
        movcs   pc, lr                /* Return if alloc_ptr >= alloc_limit */
    /* Record return address and desired size */
    /* Can use alloc_limit as a temporary since it will be reloaded by
       invoke_gc */
        ldr     alloc_limit, =caml_last_return_address
        str     lr, [alloc_limit, #0]
        ldr     alloc_limit, =caml_requested_size
        str     r12, [alloc_limit, #0]
    /* Invoke GC */
        bl      .Linvoke_gc
    /* Try again */
        ldr     r12, =caml_requested_size
        ldr     r12, [r12, #0]
        b       caml_allocN
        .type   caml_allocN, %function
        .size   caml_allocN, .-caml_allocN

/* Shared code to invoke the GC */
.Linvoke_gc:
    /* Record lowest stack address */
        ldr     r12, =caml_bottom_of_stack
        str     sp, [r12, #0]
    /* Save integer registers and return address on stack */
        stmfd   sp!, {r0,r1,r2,r3,r4,r5,r6,r7,r12,lr}
    /* Store pointer to saved integer registers in caml_gc_regs */
        ldr     r12, =caml_gc_regs
        str     sp, [r12, #0]
    /* Save current allocation pointer for debugging purposes */
        ldr     r12, =caml_young_ptr
        str     alloc_ptr, [r12, #0]
    /* Save trap pointer in case an exception is raised during GC */
        ldr     r12, =caml_exception_pointer
        str     trap_ptr, [r12, #0]
    /* Call the garbage collector */
        bl      caml_garbage_collection
    /* Restore the registers from the stack */
        ldmfd   sp!, {r0,r1,r2,r3,r4,r5,r6,r7,r12}
    /* Reload return address */
        ldr     r12, =caml_last_return_address
        ldr     lr, [r12, #0]
    /* Reload new allocation pointer and allocation limit */
        ldr     r12, =caml_young_ptr
        ldr     alloc_ptr, [r12, #0]
        ldr     r12, =caml_young_limit
        ldr     alloc_limit, [r12, #0]
    /* Return to caller */
        ldr     r12, [sp], #4
        bx      r12

/* Call a C function from Caml */
/* Function to call is in r12 */

        .globl caml_c_call
caml_c_call:
    /* Preserve return address in callee-save register r4 */
        mov     r4, lr
    /* Record lowest stack address and return address */
        ldr     r5, =caml_last_return_address
        ldr     r6, =caml_bottom_of_stack
        str     lr, [r5, #0]
        str     sp, [r6, #0]
    /* Make the exception handler and alloc ptr available to the C code */
        ldr     r6, =caml_young_ptr
        ldr     r7, =caml_exception_pointer
        str     alloc_ptr, [r6, #0]
        str     trap_ptr, [r7, #0]
    /* Call the function */
        mov     lr, pc
        bx      r12
    /* Reload alloc ptr and alloc limit */
        ldr     r5, =caml_young_limit
        ldr     alloc_ptr, [r6, #0]    /* r6 still points to caml_young_ptr */
        ldr     alloc_limit, [r5, #0]
    /* Return */
        bx      r4
        .type   caml_c_call, %function
        .size   caml_c_call, .-caml_c_call

/* Start the Caml program */

        .globl caml_start_program
caml_start_program:
        ldr     r12, =caml_program

/* Code shared with caml_callback* */
/* Address of Caml code to call is in r12 */
/* Arguments to the Caml code are in r0...r3 */

.Ljump_to_caml:
    /* Save return address and callee-save registers */
        stmfd   sp!, {r4,r5,r6,r7,r8,r10,r11,lr} /* 8-alignment */
    /* Setup a callback link on the stack */
        sub     sp, sp, #4*4                    /* 8-alignment */
        ldr     r4, =caml_bottom_of_stack
        ldr     r4, [r4, #0]
        str     r4, [sp, #0]
        ldr     r4, =caml_last_return_address
        ldr     r4, [r4, #0]
        str     r4, [sp, #4]
        ldr     r4, =caml_gc_regs
        ldr     r4, [r4, #0]
        str     r4, [sp, #8]
    /* Setup a trap frame to catch exceptions escaping the Caml code */
        sub     sp, sp, #4*2
        ldr     r4, =caml_exception_pointer
        ldr     r4, [r4, #0]
        str     r4, [sp, #0]
        ldr     r4, =.Ltrap_handler
        str     r4, [sp, #4]
        mov     trap_ptr, sp
    /* Reload allocation pointers */
        ldr     r4, =caml_young_ptr
        ldr     alloc_ptr, [r4, #0]
        ldr     r4, =caml_young_limit
        ldr     alloc_limit, [r4, #0]
    /* Call the Caml code */
        mov     lr, pc
        bx      r12
.Lcaml_retaddr:
    /* Pop the trap frame, restoring caml_exception_pointer */
        ldr     r4, =caml_exception_pointer
        ldr     r5, [sp, #0]
        str     r5, [r4, #0]
        add     sp, sp, #2 * 4
    /* Pop the callback link, restoring the global variables */
.Lreturn_result:
        ldr     r4, =caml_bottom_of_stack
        ldr     r5, [sp, #0]
        str     r5, [r4, #0]
        ldr     r4, =caml_last_return_address
        ldr     r5, [sp, #4]
        str     r5, [r4, #0]
        ldr     r4, =caml_gc_regs
        ldr     r5, [sp, #8]
        str     r5, [r4, #0]
        add     sp, sp, #4*4
    /* Update allocation pointer */
        ldr     r4, =caml_young_ptr
        str     alloc_ptr, [r4, #0]
    /* Reload callee-save registers and return */
        ldmfd   sp!, {r4,r5,r6,r7,r8,r10,r11,lr}
        bx      lr
        .type   caml_start_program, %function
        .size   caml_start_program, .-caml_start_program

    /* The trap handler */
.Ltrap_handler:
    /* Save exception pointer */
        ldr     r4, =caml_exception_pointer
        str     trap_ptr, [r4, #0]
    /* Encode exception bucket as an exception result */
        orr     r0, r0, #2
    /* Return it */
        b       .Lreturn_result

/* Raise an exception from C */

        .globl caml_raise_exception
caml_raise_exception:
    /* Reload Caml allocation pointers */
        ldr     r12, =caml_young_ptr
        ldr     alloc_ptr, [r12, #0]
        ldr     r12, =caml_young_limit
        ldr     alloc_limit, [r12, #0]
    /* Cut stack at current trap handler */
        ldr     r12, =caml_exception_pointer
        ldr     sp, [r12, #0]
    /* Pop previous handler and addr of trap, and jump to it */
        ldmfd   sp!, {trap_ptr, pc}
        .type   caml_raise_exception, %function
        .size   caml_raise_exception, .-caml_raise_exception

/* Callback from C to Caml */

        .globl caml_callback_exn
caml_callback_exn:
    /* Initial shuffling of arguments (r0 = closure, r1 = first arg) */
        mov     r12, r0
        mov     r0, r1            /* r0 = first arg */
        mov     r1, r12           /* r1 = closure environment */
        ldr     r12, [r12, #0]    /* code pointer */
        b       .Ljump_to_caml
        .type   caml_callback_exn, %function
        .size   caml_callback_exn, .-caml_callback_exn

        .globl caml_callback2_exn
caml_callback2_exn:
    /* Initial shuffling of arguments (r0 = closure, r1 = arg1, r2 = arg2) */
        mov     r12, r0
        mov     r0, r1           /* r0 = first arg */
        mov     r1, r2           /* r1 = second arg */
        mov     r2, r12          /* r2 = closure environment */
        ldr     r12, =caml_apply2
        b       .Ljump_to_caml
        .type   caml_callback2_exn, %function
        .size   caml_callback2_exn, .-caml_callback2_exn

        .globl caml_callback3_exn
caml_callback3_exn:
    /* Initial shuffling of arguments */
    /* (r0 = closure, r1 = arg1, r2 = arg2, r3 = arg3) */
        mov     r12, r0
        mov     r0, r1          /* r0 = first arg */
        mov     r1, r2          /* r1 = second arg */
        mov     r2, r3          /* r2 = third arg */
        mov     r3, r12         /* r3 = closure environment */
        ldr     r12, =caml_apply3
        b       .Ljump_to_caml
        .type   caml_callback3_exn, %function
        .size   caml_callback3_exn, .-caml_callback3_exn

        .globl caml_ml_array_bound_error
caml_ml_array_bound_error:
    /* Load address of [caml_array_bound_error] in r12 */
        ldr     r12, =caml_array_bound_error
    /* Call that function */
        b       caml_c_call
        .type   caml_ml_array_bound_error, %function
        .size   caml_ml_array_bound_error, .-caml_ml_array_bound_error

        .data
caml_requested_size:
        .word   0

/* GC roots for callback */

        .data
        .globl caml_system__frametable
caml_system__frametable:
        .word   1               /* one descriptor */
        .word   .Lcaml_retaddr  /* return address into callback */
        .short  -1              /* negative frame size => use callback link */
        .short  0               /* no roots */
        .align  2
        .type   caml_system__frametable, %object
        .size   caml_system__frametable, .-caml_system__frametable

#if defined(SYS_linux_eabi) || defined(SYS_linux_eabihf)
    /* Make stack as non-executable */
        .section .note.GNU-stack,"",%progbits
#endif
