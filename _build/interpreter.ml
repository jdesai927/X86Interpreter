(* CIS341: Project 1 Interpreter *)
(* Author: Steve Zdancewic *)

open X86

(* Int32 / Int64 abbreviations and infix arithmetic *)
let (+@) = Int32.add
let (-@) = Int32.sub
let (/@) = Int32.div
let ( *@ ) = Int32.mul
let (<@) a b = (Int32.compare a b) < 0
let (<=@) a b = (Int32.compare a b) <= 0
let (>@) a b = (Int32.compare a b) > 0
let (>=@) a b = (Int32.compare a b) >= 0
let (<@@) a b = (Int64.compare a b) < 0

exception X86_segmentation_fault of string

(* Interpret the registers as indices into the register file array *)
let eaxi = 0
let ebxi = 1
let ecxi = 2
let edxi = 3
let esii = 4
let edii = 5
let ebpi = 6
let espi = 7 

let get_register_id = function
  | Eax -> eaxi 
  | Ebx -> ebxi 
  | Ecx -> ecxi 
  | Edx -> edxi 
  | Esi -> esii 
  | Edi -> edii 
  | Ebp -> ebpi
  | Esp -> espi


let mem_size = 1024                 (* Size of memory in words *)
let mem_top : int32 = 0xfffffffcl   (* Last addressable memory location *)
let mem_bot : int32 =               (* First addressable memory location *)
	  (Int32.of_int (mem_size * 4)) *@ (-1l)

(* 
   Maps virtual addresses (int32 addresses) to physical addresses (int indices). 
   Raises an X86_segmentation_fault exception if the provided virtual address 
   does not map or if the address is unaligned. 
*)
let map_addr (addr:int32) : int =
  let a = 1023 - Int32.to_int((mem_top -@ addr) /@ 4l) in
  if Int32.rem addr 4l <> 0l || a > 1023 || a < 0
    then raise (X86_segmentation_fault "invalid") else a


type x86_state = {
    s_mem : int32 array;    (* 1024 32-bit words -- the heap *)
    s_reg : int32 array;    (* 8 32-bit words -- the register file *)
    mutable s_OF : bool;    (* overflow flag *)
    mutable s_SF : bool;    (* sign bit flag *)
    mutable s_ZF : bool;    (* zero flag *)
}

let mk_init_state () : x86_state = 
  let xs = {
  s_mem = Array.make mem_size 0l;
  s_reg = Array.make 8 0l;
  s_OF  = false;
  s_SF  = false;
  s_ZF  = false;
  } in
  xs.s_reg.(espi) <- mem_top; xs 

let print_state (xs:x86_state) : unit =
  (Array.iter (fun e -> Printf.printf "%lx " e) xs.s_mem);
  (Printf.printf "\neax: %lx ebx: %lx ecx: %lx edx: %lx" xs.s_reg.(eaxi)
      xs.s_reg.(ebxi) xs.s_reg.(ecxi) xs.s_reg.(edxi));
  (Printf.printf "\nesi: %lx edi: %lx ebp: %lx esp: %lx" xs.s_reg.(esii)
      xs.s_reg.(edii) xs.s_reg.(ebpi) xs.s_reg.(espi));
  (Printf.printf "\nOF: %b SF: %b ZF: %b\n" xs.s_OF xs.s_SF xs.s_ZF)
  

(* Helper function that determines whether a given condition code
   applies in the x86 state xs. *)  
let condition_matches (xs:x86_state) (c:X86.cnd) : bool =
  let slt = xs.s_SF <> xs.s_OF in
  let sle = slt || xs.s_ZF in
  begin match c with
    | Sge -> not slt
    | Sgt -> not sle
    | Slt -> slt
    | Sle -> sle
    | Eq -> xs.s_ZF
    | NotEq -> not xs.s_ZF
    | Zero -> xs.s_ZF
    | NotZero -> not xs.s_ZF
  end

(* Returns the bit at a given index in a 32-bit word as a boolean *)
let get_bit bitidx n =
  let shb = Int32.shift_left 1l bitidx in
  Int32.logand shb n = shb  

let reg_val (r: reg) (xs: x86_state) : int32 = xs.s_reg.(get_register_id r)

let map_default (f: 'a -> 'b) (b: 'b) (o: 'a option) : 'b =
  begin match o with
    | Some x -> f x
    | None   -> b
  end

let ind_addr (i: ind) (xs: x86_state) : int32 =
  map_default (fun r -> reg_val r xs) 0l i.i_base +@
  map_default (fun (r, y) -> y *@ reg_val r xs) 0l i.i_iscl +@
  map_default (fun d -> begin match d with
                                 | DImm im -> im
                                 | _       -> raise (X86_segmentation_fault ".")
                               end) 0l i.i_disp

let interpret_op (shift: bool) (o: opnd) (xs: x86_state) : int64 =
  Int64.of_int32 (begin match o with
    | Imm i -> i
    | Reg r -> if shift && r <> Ecx then failwith "shift must be ecx" else
                 reg_val r xs
    | Ind i -> if shift then failwith "invalid operand" else
                 xs.s_mem.(map_addr (ind_addr i xs))
    | _     -> failwith "should not be reached"
  end)

let interpret_dest (o: opnd) (xs: x86_state) : int32 array * int =
  begin match o with
    | Reg r -> xs.s_reg, get_register_id r
    | Ind i -> xs.s_mem, map_addr (ind_addr i xs)
    | _     -> raise (X86_segmentation_fault "Invalid dest")
  end

let rec interpret_insn (inst: insn) (xs: x86_state) : unit =
  let same_sign_d i1 i2 = (i2 <@ 0l && i1 <@@ 0L) || (0l <@ i2 && 0L <@@ i1) in
  let same_sign i1 i2 = (i1 <@@ 0L && i2 <@@ 0L) || (0L <@@ i1 && 0L <@@ i2) in
  let flg_set o r = xs.s_OF <- o; xs.s_SF <- r <@ 0l; xs.s_ZF <- r = 0l in
  let un_op f x =
    let a, d = interpret_dest x xs in
    let op = interpret_op false x xs in
    let r = f op in
    a.(d) <- Int64.to_int32 r;
    r, op in
  (*We couldn't reuse bin_op for shifting because of the sign
    extension issue. *)
  let shift_op f x y = 
    let a, i = interpret_dest x xs in
    let d = Int64.to_int32 (interpret_op false x xs) in
    let s = Int64.to_int32 (interpret_op true y xs) in
    let res = f d s in
    a.(i) <- res;
    res, d, s in
  let bin_op f x y =
    let a, i = interpret_dest x xs in
    let d = interpret_op false x xs in
    let s = interpret_op false y xs in
    let res = f d s in
    a.(i) <- Int64.to_int32 res;
    res, d, s in
  begin match inst with
    | Add (o1, o2) -> let r, d, s = bin_op Int64.add o1 o2 in
                      let r32 = Int64.to_int32 r in
                      flg_set (same_sign s d && not (same_sign_d s r32)) r32
    | Neg o        -> let r, op = un_op Int64.neg o in
                      let op32 = Int64.to_int32 op in
                      flg_set (op32 = Int32.min_int) (Int64.to_int32 r)
    | Sub (o1, o2) -> let r, d, s = bin_op Int64.sub o1 o2 in
                      let r32 = Int64.to_int32 r in
                      let ms = Int64.neg s in
                      flg_set (same_sign d ms && not (same_sign_d ms r32) ||
                                 Int64.to_int32 s = Int32.min_int) r32
    | Lea (r, i)   -> xs.s_reg.(get_register_id r) <- ind_addr i xs
    | Mov (o1, o2) -> let (a, d) = interpret_dest o1 xs in
                      a.(d) <- Int64.to_int32 (interpret_op false o2 xs)
    | Shl (o1, o2) -> let r, d, s = 
      shift_op (fun i1 i2 -> Int32.shift_left i1 (Int32.to_int i2)) o1 o2 in
      flg_set (if s = 1l then (get_bit 31 d <> get_bit 30 d) || 
                  xs.s_OF else xs.s_OF) r
    | Sar (o1, o2) -> let r, _, s = 
      shift_op (fun i1 i2 -> Int32.shift_right i1 (Int32.to_int i2)) o1 o2 in
      flg_set (s <> 1l && xs.s_OF) r
    | Shr (o1, o2) -> let r, d, s =
      shift_op (fun i1 i2 -> 
        Int32.shift_right_logical i1 (Int32.to_int i2)) o1 o2 in
      flg_set (if s = 1l then get_bit 31 d else xs.s_OF) r
    | Not o        -> let _, _ = un_op Int64.lognot o in
                      ()
    | And (o1, o2) -> let r, _, _ = bin_op Int64.logand o1 o2 in
                      let r32 = Int64.to_int32 r in
                      flg_set false r32
    | Or (o1, o2)  -> let r, _, _ = bin_op Int64.logor o1 o2 in
                      let r32 = Int64.to_int32 r in
                      flg_set false r32
    | Xor (o1, o2) -> let r, _, _ = bin_op Int64.logxor o1 o2 in
                      let r32 = Int64.to_int32 r in
                      flg_set false r32
    | Push o       -> xs.s_reg.(espi) <- xs.s_reg.(espi) -@ 4l;
                      xs.s_mem.(map_addr (xs.s_reg.(espi))) <- 
                        Int64.to_int32 (interpret_op false o xs)
    | Pop o        -> if xs.s_reg.(espi) = mem_top then 
                        raise (X86_segmentation_fault "nothing to pop");
                      let a, d = interpret_dest o xs in
                      a.(d) <- xs.s_mem.(map_addr(xs.s_reg.(espi)));
                      xs.s_reg.(espi) <- xs.s_reg.(espi) +@ 4l
    | Cmp (o1, o2) -> let d = interpret_op false o1 xs in
                      let s = interpret_op false o2 xs in
                      let r32 = Int64.to_int32 (Int64.sub d s) in
                      let ms = Int64.neg s in
                      flg_set (same_sign d ms && not (same_sign_d ms r32) ||
                                 Int64.to_int32 s = Int32.min_int) r32
    | Setb (o, c)  -> let a, d = interpret_dest o xs in
		      let r = interpret_op false o xs in
		      a.(d) <- Int64.to_int32 (Int64.shift_left (Int64.shift_right r 8) 8) +@
			if condition_matches xs c then 1l else 0l
    | Imul (rg, o) -> 
      let r = Int64.mul (Int64.of_int32 (reg_val rg xs)) (interpret_op false o xs) in
      let r32 = Int64.to_int32 r in
      xs.s_reg.(get_register_id rg) <- r32;    
      flg_set (r <> Int64.of_int32 r32) r32
    | _            -> failwith "should not be reached"
  end

let interpret (code:insn_block list) (xs:x86_state) (l:lbl) : unit =

  let find_block la = (List.find (fun i -> i.label = la) code).insns in

  let get_lbl o =
    begin match o with
      | Lbl l -> l
      | _ -> raise (X86_segmentation_fault "Call/Jmp to non-label")
    end
  in

  let rec insn_loop li stk =
    if li <> [] then
      let h, t = List.hd li, List.tl li in
      begin match h with
        | Ret      -> xs.s_reg.(espi) <- xs.s_reg.(espi) +@ 4l;
                      if stk <> [] then insn_loop (List.hd stk) (List.tl stk)
        | Jmp o    -> insn_loop (find_block (get_lbl o)) stk
        | Call o   -> interpret_insn (Push (Imm 0l)) xs;
                      insn_loop (find_block (get_lbl o)) (t::stk)
        | J (c, l) -> 
          insn_loop (if condition_matches xs c then find_block l else t) stk
        | _ -> interpret_insn h xs; insn_loop t stk
      end
  in
  insn_loop (find_block l) []
      
let run (code:insn_block list) : int32 =
  let main = X86.mk_lbl_named "main" in
  let xs = mk_init_state () in
  let _ = interpret code xs main in
    xs.s_reg.(eaxi)
      
