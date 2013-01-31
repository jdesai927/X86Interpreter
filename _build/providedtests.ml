open Assert
open X86
open Interpreter
open Gradedtests

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let test_sf (f: unit -> 'a) () : unit =
  try ignore (f ());
    failwith "Should have raised an X86_segmentation_fault"
  with
    | X86_segmentation_fault _ -> ()
    | _ -> failwith "Should have raised an X86_segmentation_fault"


let provided_tests : suite = [
  Test ("Student-Provided Big Test for Part II", 
	[("x mod y 2", run_test 4l [
	   (mk_insn_block (mk_lbl_named "mod_aux") [
	     Sub (eax, ebx);
	     Call (Lbl (mk_lbl_named "mod_recurse"));	    
	     Ret;
	  ]);
	   (mk_insn_block (mk_lbl_named "mod_recurse") [
	     Cmp (eax, ebx);
	     J (Sge, mk_lbl_named "mod_aux");
	     Ret;
	  ]);
	   (mk_insn_block (mk_lbl_named "mod") [
	     Push (ebp);
	     Mov (ebp, esp);
	     Mov (ebx, stack_offset 12l);
	     Mov (eax, stack_offset 8l);
	     Jmp (Lbl (mk_lbl_named "mod_recurse"));
	  ]);
	   (mk_insn_block (mk_lbl_named "main") [
	     Push (Imm 5l);
	     Push (Imm 94l);
	     Call (Lbl (mk_lbl_named "mod"));
	     Add (esp, Imm 8l);
	     Ret;
	  ]);])
	]);  

  Test ("Additional Test", 
	[("x mod y", run_test 4l [
	   (mk_insn_block (mk_lbl_named "done") [
	     Cmp (ecx, ebx);
	     J (Slt, mk_lbl_named "skip");
	     Ret;
	  ]);
	   (mk_insn_block (mk_lbl_named "skip") [
	     Jmp (Lbl (mk_lbl_named "finish"));
	  ]);
	   (mk_insn_block (mk_lbl_named "loop") [
	     Sub (ecx, ebx);
	     Call (Lbl (mk_lbl_named "done"));
	     Ret;
	  ]);
	   (mk_insn_block (mk_lbl_named "main") [
	     Mov (eax, Imm 94l);
	     Mov (ebx, Imm 5l);
	     Mov (ecx, eax);
	     Jmp (Lbl (mk_lbl_named "run"));
	  ]);
	   (mk_insn_block (mk_lbl_named "run") [
	     Call (Lbl (mk_lbl_named "loop"));
             Jmp (Lbl (mk_lbl_named "run"))
	  ]);
	   (mk_insn_block (mk_lbl_named "finish") [
	     Mov (eax, ecx);
	  ]);])
	]);
  
  Test ("Tate and Jinesh's Little Tests", [
    ("test pop segfault", test_sf 
      (fun () -> interpret [(mk_insn_block (mk_lbl_named "main") [
	Pop (eax);
	Ret;
      ])] (mk_init_state ()) (mk_lbl_named "main"))
    );
    ("test pop segfault", test_sf 
      (fun () -> interpret [(mk_insn_block (mk_lbl_named "main") [
	Push (Imm 13l);
	Push (Imm 10l);
	Push (Imm 4l);
	Push (Imm 3l);
	Pop (eax);
	Pop (ebx);
	Pop (ecx);
	Pop (edx);
	Pop (eax);
	Ret;
      ])] (mk_init_state ()) (mk_lbl_named "main"))
    );
    ("test cs-shl", cs_test [(mk_block "main" [
      Mov (eax, Imm (Int32.min_int));
      Shl (eax, Imm 1l);
      Ret;
      ])] (true, false, true)
    );
    ("test cs-sar", cs_test [(mk_block "main" [
      Mov (eax, Imm Int32.max_int);
      Sar (eax, Imm 1l);
      Ret;
     ])] (false, false, false)
    );
    ("test cs-shr zf", cs_test [(mk_block "main" [
      Mov (ecx, Imm 1l);
      Mov (eax, Imm 0l);
      Shr (eax, ecx);
      Ret;
     ])] (false, false, true)
    );
    ("test cs-shr of", cs_test [(mk_block "main" [
      Mov (eax, Imm 0x80000000l);
      Shr (eax, Imm 1l);
      Ret;
     ])] (true, false, false) 
    );
    ("test cs-shr of - amt not 1", cs_test [(mk_block "main" [
      Mov (eax, Imm (Int32.min_int));
      Shl (eax, Imm 1l);
      Mov (eax, Imm 0x00FFFFF0l);
      Shr (eax, Imm 4l);
      Ret;
     ])] (true, false, false)
    );
    
])]
