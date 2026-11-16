/* A bare guest: everything in one run of memory from 2 MiB, the entry first. */
ENTRY(_start)
SECTIONS {
  . = 0x200000;
  .text : { *(.text.start) *(.text .text.*) }
  . = ALIGN(4096);
  .rodata : { *(.rodata .rodata.*) }
  . = ALIGN(4096);
  .data : { *(.data .data.*) }
  .bss : { *(.bss .bss.*) *(COMMON) }
  /DISCARD/ : { *(.eh_frame*) *(.comment) *(.note*) }
}
