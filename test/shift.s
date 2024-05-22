  .org $8000
reset:
  ldx #10
  lda #1
  ldy #0

loop:
  cpy #0
  bne rol
  clc
  jmp no
rol:
  sec
no:
  rol

  sta $2001

  bcc nocarry
  ldy #1
  jmp next
nocarry:
  ldy #0
next:

  dex
  cpx #0
  bne loop

  .org $fffc
  .word reset
  .word $0000

