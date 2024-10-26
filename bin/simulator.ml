(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L (* lowest valid address *)
let mem_top = 0x410000L (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17 (* including Rip *)
let ins_size = 8L (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL (* halt when m.regs(%rip) = exit_addr *)

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
   at&t syntax             ocaml syntax
   movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
   decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

   0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
   0x400001 :  InsFrag
   0x400002 :  InsFrag
   0x400003 :  InsFrag
   0x400004 :  InsFrag
   0x400005 :  InsFrag
   0x400006 :  InsFrag
   0x400007 :  InsFrag
   0x400008 :  InsB0 (Decq,  [~%Rdi])
   0x40000A :  InsFrag
   0x40000B :  InsFrag
   0x40000C :  InsFrag
   0x40000D :  InsFrag
   0x40000E :  InsFrag
   0x40000F :  InsFrag
   0x400010 :  InsFrag
*)
type sbyte =
  | InsB0 of ins (* 1st byte of an instruction *)
  | InsFrag (* 2nd - 8th bytes of an instruction *)
  | Byte of char (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags =
  { mutable fo : bool
  ; mutable fs : bool
  ; mutable fz : bool
  }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach =
  { flags : flags
  ; regs : regs
  ; mem : mem
  }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0
  | Rbx -> 1
  | Rcx -> 2
  | Rdx -> 3
  | Rsi -> 4
  | Rdi -> 5
  | Rbp -> 6
  | Rsp -> 7
  | R08 -> 8
  | R09 -> 9
  | R10 -> 10
  | R11 -> 11
  | R12 -> 12
  | R13 -> 13
  | R14 -> 14
  | R15 -> 15
;;

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i : int64) : sbyte list =
  let open Char in
  let open Int64 in
  List.map
    (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
    [ 0; 8; 16; 24; 32; 40; 48; 56 ]
;;

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs : sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i =
    match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L
;;

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s : string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i] :: acc) (Int.pred i)
  in
  loop [ Byte '\x00' ] @@ (String.length s - 1)
;;

(* Serialize an instruction to sbytes *)
let sbytes_of_ins ((op, args) : ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) ->
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | _ -> ()
  in
  List.iter check args;
  [ InsB0 (op, args); InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag ]
;;

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"
;;

(* It might be useful to toggle printing of intermediate states of your
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

   [if !debug_simulator then print_endline @@ string_of_ins u; ...]
*)
let debug_simulator = ref false

(* override some useful operators *)
let ( +. ) = Int64.add
let ( -. ) = Int64.sub
let ( *. ) = Int64.mul
let ( <. ) a b = Int64.compare a b < 0
let ( >. ) a b = Int64.compare a b > 0
let ( <=. ) a b = Int64.compare a b <= 0
let ( >=. ) a b = Int64.compare a b >= 0

(* Interpret a condition code with respect to the given flags. *)
(* !!! Check the Specification for Help *)
let interp_cnd { fo; fs; fz } : cnd -> bool =
  fun x ->
  match x with
  | Eq -> fz
  | Neq -> not fz
  | Gt -> fo = fs && not fz
  | Lt -> fo <> fs
  | Ge -> fo = fs
  | Le -> fo <> fs || fz
;;

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr : quad) : int option =
  let open Int64 in
  let i = to_int (sub addr mem_bot) in
  if i < 0 || i >= mem_size then None else Some i
;;

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* Raise X86lite_segfault when addr is invalid. *)
let map_addr_segfault (addr : quad) : int =
  let result = map_addr addr in
  match result with
  | Some i -> i
  | None -> raise X86lite_segfault
;;

(* Simulates one step of the machine:
   - fetch the instruction at %rip
   - compute the source and/or destination information from the operands
   - simulate the instruction semantics
   - update the registers and/or memory appropriately
   - set the condition flags

   We provide the basic structure of step function and helper functions.
   Implement the subroutine below to complete the step function.
   See step function to understand each subroutine and how they
   are glued together.
*)
let fetch_addr_val (m : mach) (addr : quad) : sbyte list =
  (* let i = map_addr addr in
     match i with
     | Some i ->
     [ (* TODO: change it into function style *)
      m.mem.(i)
    ; m.mem.(i + 1)
    ; m.mem.(i + 2)
    ; m.mem.(i + 3)
    ; m.mem.(i + 4)
    ; m.mem.(i + 5)
    ; m.mem.(i + 6)
    ; m.mem.(i + 7)
    ]
     | None -> raise X86lite_segfault *)
  (* Use map_addr_segfault and change into functional style Iter *)
  let i = map_addr_segfault addr in
  List.init 8 (fun idx -> m.mem.(i + idx))
;;

let readquad (m : mach) (addr : quad) : quad = int64_of_sbytes (fetch_addr_val m addr)

let writequad (m : mach) (addr : quad) (w : quad) : unit =
  (* let array_index = map_addr addr in
     match array_index with
     | Some i ->
     let sbytes = sbytes_of_int64 w in
     m.mem.(i) <- List.nth sbytes 0;
     m.mem.(i + 1) <- List.nth sbytes 1;
     m.mem.(i + 2) <- List.nth sbytes 2;
     m.mem.(i + 3) <- List.nth sbytes 3;
     m.mem.(i + 4) <- List.nth sbytes 4;
     m.mem.(i + 5) <- List.nth sbytes 5;
     m.mem.(i + 6) <- List.nth sbytes 6;
     m.mem.(i + 7) <- List.nth sbytes 7
     (* List.iteri (fun idx byte ->
     m.mem.(i + idx) <- byte
     ) (List.take 8 sbytes) *)
     | None -> raise X86lite_segfault *)
  let i = map_addr_segfault addr in
  let sbytes = sbytes_of_int64 w in
  List.iteri (fun idx byte -> m.mem.(i + idx) <- byte) sbytes
;;

(* Implement the interpretation of operands (including indirect
   addresses), since this functionality will be needed for
   simulating instructions.*)
let rec interp_operand (m : mach) : operand -> int64 = function
  | Imm i ->
    (match i with
     | Lit l -> l
     | Lbl _ -> invalid_arg "interp_operand: tried to interpret a label!")
  | Reg r -> m.regs.(rind r)
  (* addr(Ind) = Base + [Index * Scale] + Disp*)
  | Ind1 r ->
    let litr = interp_operand m (Imm r) in
    let addr = litr in
    readquad m addr
  | Ind2 r ->
    let addr = m.regs.(rind r) in
    readquad m addr
  | Ind3 (r1, r2) ->
    let addr = Int64.add m.regs.(rind r2) (interp_operand m (Imm r1)) in
    readquad m addr
;;

let rec save_data (m : mach) (data : int64) (dest : operand) : unit =
  match dest with
  | Ind1 _ | Ind2 _ | Ind3 _ ->
    let addr =
      match dest with
      | Ind1 r -> interp_operand m (Imm r)
      | Ind2 r -> m.regs.(rind r)
      | Ind3 (r1, r2) -> Int64.add m.regs.(rind r2) (interp_operand m (Imm r1))
      | _ -> failwith "save_data: unsupported destination operand"
    in
    writequad m addr data
  | Reg r -> m.regs.(rind r) <- data
  | Imm (Lit i) ->
    let addr = Int64.add m.regs.(rind Rip) ins_size in
    writequad m addr i
  | _ -> failwith "save_data: unsupported destination operand"
;;

let fetchins (m : mach) (addr : quad) : ins =
  (* if !debug_simulator then Printf.printf "fetchins: addr = %Lx\n" addr; *)
  let inst = fetch_addr_val m addr in
  match inst with
  | InsB0 (op, args) :: _ -> op, args
  | InsFrag :: _ -> failwith "fetchins: should not be frag"
  | _ ->
    (* if !debug_simulator then Printf.printf "fetchins: Error on %s\n" (Int64.to_string addr); *)
    failwith ("fetchins: malformed instruction " ^ Int64.to_string addr ^ ", inst:" ^ Int64.to_string @@ int64_of_sbytes inst)
;;

(* Compute the instruction result.
 * NOTE: See int64_overflow.ml for the definition of the return type
 *  Int64_overflow.t. *)
let interp_opcode (m : mach) (o : opcode) (args : int64 list) : Int64_overflow.t =
  let open Int64 in
  let open Int64_overflow in
  match o, args with
  | Movq, [ src; _ ] -> { value = src; overflow = false }
  | Leaq, [ ind; _ ] -> { value = ind; overflow = false }
  | (Negq | Incq | Decq), [ dest ] ->
    (match o with
     | Negq -> neg dest
     | Incq -> add dest 1L
     | Decq -> sub dest 1L
     | _ -> failwith "interp_opcode: unsupported instruction")
  | (Addq | Subq | Imulq), [ src; dest ] ->
    (match o with
     | Addq -> add dest src
     | Subq -> sub dest src
     | Imulq -> mul dest src
     | _ -> failwith "interp_opcode: unsupported instruction")
  | Notq, [ dest ] -> { value = lognot dest; overflow = false }
  | (Xorq | Orq | Andq), [ src; dest ] ->
    (match o with
     | Xorq -> { value = logxor dest src; overflow = false }
     | Orq -> { value = logor dest src; overflow = false }
     | Andq -> { value = logand dest src; overflow = false }
     | _ -> failwith "interp_opcode: unsupported instruction")
  | (Sarq | Shlq | Shrq), [ i; dest ] ->
    (match o with
     | Sarq -> { value = shift_right dest (to_int i); overflow = false }
     | Shlq -> { value = shift_left dest (to_int i); overflow = false }
     | Shrq -> { value = shift_right_logical dest (to_int i); overflow = false }
     | _ -> failwith "interp_opcode: unsupported instruction")
  | Set c, [ src ] ->
    let b = interp_cnd m.flags c in
    let bit = if b then 1L else 0L in
    let lowest = logand src 0xffffffffffffff00L in
    ok (logor lowest bit)
  | Cmpq, [ src1; src2 ] -> sub src2 src1
  | J c, [ src ] ->
    (* TODO: *)
    let b = interp_cnd m.flags c in
    if b
    then { value = src; overflow = false }
    else { value = m.regs.(rind Rip); overflow = false }
  | Jmp, [ src ] -> { value = src; overflow = false }
  | (Pushq | Popq | Callq | Retq), _ -> failwith "interp_opcode: should not reach here"
  | _ -> failwith "interp_opcode: unsupported instruction"
;;

(** Update machine state with instruction results. *)
let ins_writeback (m : mach) (instr : ins) (value : int64) : unit =
  match instr with
  | (Negq | Incq | Decq | Notq), [ dest ] -> save_data m value dest
  | (Addq | Subq | Andq | Imulq | Orq | Xorq | Movq), [ _; dest ] ->
    save_data m value dest
  | (Sarq | Shlq | Shrq), [ _; dest ] -> save_data m value dest
  | (Pushq | Jmp | Callq), [ _ ] -> m.regs.(rind Rip) <- value
  | Popq, [ dest ] -> save_data m value dest
  | (Set _), [ dest ] -> save_data m value dest
  | (J _), [ _ ] -> m.regs.(rind Rip) <- value
  | Cmpq, [ _; _ ] -> ()
  | Leaq, [ _; dest ] -> save_data m value dest
  (* | Imulq, [ _; Reg _ ] -> m.regs.(rind Rax) <- value *)
  | Retq, [] -> m.regs.(rind Rip) <- value
  | _ -> failwith "ins_writeback: unsupported instruction"
;;

(* mem addr ---> mem array index *)
let interp_operands (m : mach) : ins -> int64 list =
  let open List in
  let open Int64 in
  function
  | (Negq | Incq | Decq | Notq), [ dest ] -> [ interp_operand m dest ]
  | (Addq | Subq | Andq | Imulq | Orq | Xorq | Movq | Sarq | Shlq | Shrq), [ src; dest ]
    -> [ interp_operand m src; interp_operand m dest ]
  (* | (Sarq | Shlq | Shrq), [ Imm (Lit i); dest ] -> [ i; interp_operand m dest ] *)
  | (Pushq | Jmp | Callq), [ src ] -> [ interp_operand m src ]
  | Popq, [ src ] -> [ interp_operand m src ]
  | (J _ | Set _), [ src ] -> [ interp_operand m src ]
  | Cmpq, [ src1; src2 ] -> [ interp_operand m src1; interp_operand m src2 ]
  | Leaq, [ ind; dest ] -> [ interp_operand m ind; interp_operand m dest ]
  (* | Imulq, [ src; Reg _ ] -> [ interp_operand m src ] *)
  | Retq, [] -> []
  | _ -> failwith "interp_operands: unsupported instruction"
;;

let validate_operands : ins -> unit = function
  | (Negq | Incq | Decq | Notq), [ dest ] ->
    (match dest with
     | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'dest'")
  | (Addq | Subq | Andq | Imulq | Orq | Xorq | Movq | Sarq | Shlq | Shrq), [ src; dest ]
    ->
    (match src with
     | Imm (Lit _) | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'src'");
    (match dest with
     | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'dest'")
  (* | (Sarq | Shlq | Shrq), [ Imm (Lit _); dest ] ->
     (match dest with
     | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'dest'") *)
  | (Pushq | Jmp | Callq), [ src ] ->
    (match src with
     | Imm (Lit _) | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'src'")
  | Popq, [ src ] ->
    (match src with
     | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'src'")
  | (J _ | Set _), [ src ] ->
    (match src with
     | Imm (Lit _) | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'src'")
  | Cmpq, [ src1; src2 ] ->
    (match src1 with
     | Imm (Lit _) | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'src1'");
    (match src2 with
     | Imm (Lit _) | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'src2'")
  | Leaq, [ ind; dest ] ->
    (match ind with
     | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'ind'");
    (match dest with
     | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'dest'")
  (* | Imulq, [ src; Reg _ ] ->
     (match src with
     | Imm (Lit _) | Reg _ | Ind1 _ | Ind2 _ | Ind3 _ -> ()
     | _ -> failwith "validate_operands: unsupported operand 'src'")*)
  | Retq, [] -> ()
  | _ -> failwith "validate_operands: unsupported instruction"
;;

(* Split instruction to smaller instructions *)
let rec crack : ins -> ins list = function
  | Pushq, [ src ] -> [ Subq, [ Imm (Lit 8L); Reg Rsp ]; Movq, [ src; Ind2 Rsp ] ]
  | Popq, [ dest ] -> [ Movq, [ Ind2 Rsp; dest ]; Addq, [ Imm (Lit 8L); Reg Rsp ] ]
  | Callq, [ src ] -> crack (Pushq, [ Reg Rip ]) @ [ Jmp, [ src ] ]
  | Retq, [] -> crack (Popq, [ Reg Rip ])
  | _ as ins -> [ ins ]
;;

(* TODO: double check against spec *)
let set_flags (m : mach) (op : opcode) (ws : quad list) (w : Int64_overflow.t) : unit =
  match op with
  | Negq | Incq | Decq | Addq | Subq | Imulq | Cmpq ->
    m.flags.fo <- w.overflow;
    m.flags.fs <- w.value <. 0L;
    m.flags.fz <- w.value = 0L
  | Xorq | Orq | Andq ->
    m.flags.fo <- false;
    m.flags.fs <- w.value <. 0L;
    m.flags.fz <- w.value = 0L
  | Sarq | Shlq | Shrq ->
    (* m.flags.fo <- false; *)
    m.flags.fs <- w.value <. 0L;
    m.flags.fz <- w.value = 0L
  | _ -> ()
;;

let step (m : mach) : unit =
  (* execute an instruction *)
  let ((op, args) as ins) = fetchins m m.regs.(rind Rip) in
  validate_operands ins;
  (* Some instructions involve running two or more basic instructions. 
   * For other instructions, just return a list of one instruction.
   * See the X86lite specification for details. *)
  let uops : ins list = crack (op, args) in
  m.regs.(rind Rip) <- m.regs.(rind Rip) +. ins_size;
  List.iter
    (fun ((uop, _) as u) ->
      if !debug_simulator then print_endline @@ string_of_ins u;
      let ws = interp_operands m u in
      let res = interp_opcode m uop ws in
      ins_writeback m u @@ res.Int64_overflow.value;
      set_flags m op ws res)
    uops
;;

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the
   machine halts. *)
let run (m : mach) : int64 =
  while m.regs.(rind Rip) <> exit_addr do
    if !debug_simulator then Printf.printf "Rip: %Lx; Rsp: %Lx, Rdi: %Lx, flags: [fo: %b; fs: %b; fz: %b]\n" m.regs.(rind Rip) m.regs.(rind Rsp) m.regs.(rind Rdi) m.flags.fo m.flags.fs m.flags.fz;
    step m;
    if !debug_simulator && List.nth (fetch_addr_val  m 0x400036L) 0 <> InsFrag then
      Printf.printf "CHANGED!!!\n";

  done;
  m.regs.(rind Rax)
;;

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec =
  { entry : quad (* address of the entry point *)
  ; text_pos : quad (* starting address of the code *)
  ; data_pos : quad (* starting address of the data *)
  ; text_seg : sbyte list (* contents of the text segment *)
  ; data_seg : sbyte list (* contents of the data segment *)
  }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
     Note: the size of an Asciz string section is (1 + the string length)
     due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to
     replace Lbl values with the corresponding Imm values.
     HINT: consider building a mapping from symboli Lbl to memory address

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

   HINT: List.fold_left and List.fold_right are your friends.
*)
let is_size (is : ins list) : quad = List.fold_left (fun acc _ -> acc +. ins_size) 0L is

let ds_size (ds : data list) : quad =
  List.fold_left
    (fun acc -> function
      | Quad _ -> acc +. 8L
      | Asciz s -> acc +. Int64.of_int (String.length s + 1))
    0L
    ds
;;

type label_data =
  { base : quad
  ; hashtbl : (lbl, quad) Hashtbl.t
  }

let parse_labels (elem_list : elem list) (base_addr : quad) : (lbl, quad) Hashtbl.t =
  let tbl = Hashtbl.create @@ List.length elem_list in
  let _ =
    List.fold_left
      (fun data { lbl; asm; _ } ->
        if Hashtbl.mem tbl lbl then raise (Redefined_sym lbl);
        let size =
          match asm with
          | Text is -> is_size is
          | Data ds -> ds_size ds
        in
        Hashtbl.add tbl lbl data.base;
        { base = data.base +. size; hashtbl = tbl })
      { base = base_addr; hashtbl = tbl }
      elem_list
  in
  tbl
;;

let find_label (tbl : (lbl, quad) Hashtbl.t) (lbl : lbl) : quad =
  match Hashtbl.find_opt tbl lbl with
  | Some addr -> addr
  | None -> raise (Undefined_sym lbl)
;;

let resolve_labels (elem_list : ins list) (tbl : (lbl, quad) Hashtbl.t) : ins list =
  let find_and_raise = find_label tbl in
  let resolve_operand (op : operand) : operand =
    match op with
    | Imm (Lbl l) -> Imm (Lit (find_and_raise l))
    | Ind1 (Lbl l) -> Ind1 (Lit (find_and_raise l))
    | Ind3 (Lbl l, r) -> Ind3 (Lit (find_and_raise l), r)
    | _ -> op
  in
  let resolve_ins (op, args) : ins = op, List.map resolve_operand args in
  List.map resolve_ins elem_list
;;

let assemble (p : prog) : exec =
  let text, data =
    List.partition
      (fun { asm; _ } ->
        match asm with
        | Text _ -> true
        | _ -> false)
      p
  in
  let text_list =
    List.fold_left
      (fun acc { asm; _ } ->
        match asm with
        | Text is -> acc @ is
        | _ -> acc)
      []
      text
  and data_list =
    List.fold_left
      (fun acc { asm; _ } ->
        match asm with
        | Data ds -> acc @ ds
        | _ -> acc)
      []
      data
  in
  let text_size = is_size text_list
  and data_size = ds_size data_list in
  let text_pos = mem_bot in
  let data_pos = mem_bot +. text_size in
  let hash_tbl = parse_labels (text @ data) text_pos in
  let entry = find_label hash_tbl "main" in
  let text_seg =
    List.flatten @@ List.map sbytes_of_ins (resolve_labels text_list hash_tbl)
  and data_seg = List.flatten @@ List.map sbytes_of_data data_list in
  { entry; text_pos; data_pos; text_seg; data_seg }
;;

(* Convert an object file into an executable machine state.
   - allocate the mem array
   - set up the memory state by writing the symbolic bytes to the
     appropriate locations
   - create the inital register state
   - initialize rip to the entry point address
   - initializes rsp to the last word in memory
   - the other registers are initialized to 0
   - the condition code flags start as 'false'

   Hint: The Array.make, Array.blit, and Array.of_list library functions
   may be of use.
*)
let load { entry; text_pos; data_pos; text_seg; data_seg } : mach =
  let mem = Array.make mem_size InsFrag in
  let _ =
    List.iteri
      (fun i byte ->
        mem.(i)
        <- (match byte with
            | InsB0 (op, args) -> InsB0 (op, args)
            | InsFrag -> InsFrag
            | Byte c -> Byte c))
      (text_seg @ data_seg)
  in
  let regs = Array.make nregs 0L in
  regs.(rind Rip) <- entry;
  regs.(rind Rsp) <- mem_top -. 8L;
  (* exit_addr magic number in mem_top-8 *)
  writequad
    { flags = { fo = false; fs = false; fz = false }; regs; mem }
    (mem_top -. 8L)
    exit_addr;
  if !debug_simulator then print_endline "Loaded machine state";
  { flags = { fo = false; fs = false; fz = false }; regs; mem }
;;
