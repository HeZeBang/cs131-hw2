open Util.Assert
open X86
open Sim.Simulator
open Gradedtests
open Asm 
(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)


let test_my =
  let bin = [
    InsB0 (Movq, Asm.[ ~$42; ~%Rax ]);
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    ] 
  
  in 

  let asm =  [gtext "main"
  [ 
    Movq,  [~$42; ~%Rax]];
  ] in 

  (assert_eqf (fun() ->  (assemble asm).text_seg) bin )

 
let mov_ri =
 test_machine
 [
 InsB0 (Movq, Asm.[ ~$42; ~%Rax ]);
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 ]

let hanoi n src tmp dst = 
  [
    text "hanoi"
      [
        Pushq, [~%Rbp]
      ; Movq, [~%Rsp; ~%Rbp]
      ; Subq, [~$32; ~%Rsp]
      ; Movq, [~%Rdi; Ind3(Lit (Int64.neg 8L), Rbp)]
      ; Movq, [~%Rsi; Ind3(Lit (Int64.neg 16L), Rbp)]
      ; Movq, [~%Rdx; Ind3(Lit (Int64.neg 24L), Rbp)]
      ; Movq, [~%Rcx; Ind3(Lit (Int64.neg 32L), Rbp)]
      ; Cmpq, [~$1; Ind3(Lit (Int64.neg 8L), Rbp)]
      ; J Neq, [~$$"hanoi_rec"]
      ; Incq, [~%Rbx]
      ; Jmp, [~$$"hanoi_end"]
      ]
    ; text "hanoi_rec"
      [
        Movq, [Ind3(Lit (Int64.neg 8L), Rbp); ~%Rdi]
      ; Decq, [~%Rdi]
      ; Movq, [Ind3(Lit (Int64.neg 16L), Rbp); ~%Rsi]
      ; Movq, [Ind3(Lit (Int64.neg 32L), Rbp); ~%Rdx]
      ; Movq, [Ind3(Lit (Int64.neg 24L), Rbp); ~%Rcx]
      ; Callq, [~$$"hanoi"]
      ; Incq, [~%Rbx]
      ; Movq, [Ind3(Lit (Int64.neg 8L), Rbp); ~%Rdi]
      ; Decq, [~%Rdi]
      ; Movq, [Ind3(Lit (Int64.neg 24L), Rbp); ~%Rsi]
      ; Movq, [Ind3(Lit (Int64.neg 16L), Rbp); ~%Rdx]
      ; Movq, [Ind3(Lit (Int64.neg 32L), Rbp); ~%Rcx]
      ; Callq, [~$$"hanoi"]
      ]
    ; text "hanoi_end"
      [
        Addq, [~$32; ~%Rsp]
      ; Popq, [~%Rbp]
      ; Retq, []
      ]
    ; gtext "main"
      [
        Pushq, [~%Rbp]
      ; Xorq, [~%Rbx; ~%Rbx]
      ; Movq, [~%Rsp; ~%Rbp]
      ; Movq, [~$3; ~%Rdi]
      ; Movq, [~$0; ~%Rsi]
      ; Movq, [~$1; ~%Rdx]
      ; Movq, [~$2; ~%Rcx]
      ; Callq, [~$$"hanoi"]
      ; Movq, [~%Rbx; ~%Rax]
      ; Popq, [~%Rbp]
      ; Retq, []
      ]
  ]

let provided_tests : suite = [
  
  Test ("My Tests", [
    ("assert", test_my)
  ]);

  Test ("Student-Provided Big Test for Part III: Score recorded as PartIIITestCase", [
    ("hanoi-5", program_test (hanoi 3 0 1 2) 7L); 
    ("hanoi-7", program_test (hanoi 5 0 1 2) 7L) 
  ]);

] 
