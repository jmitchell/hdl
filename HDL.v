Require Import String.
Require Import List.

Open Scope string_scope.
Import ListNotations.


Definition chip_name : Set := string.
Definition pin_name : Set := string.

Inductive connection : Set :=
| Connection : pin_name -> pin_name -> connection
| ConstSignal : pin_name -> bool -> connection.

Inductive connections : Set :=
| Connections : list connection -> connections.

Inductive part : Set :=
| InternalChip : chip_name -> connections -> part.

Inductive parts : Set :=
| Parts : list part -> parts.

Inductive pin : Set :=
| Pin : pin_name -> pin.

Inductive inputs : Set :=
| Inputs : list pin -> inputs.

Inductive outputs : Set :=
| Outputs : list pin -> outputs.

Inductive chip_interface : Set :=
| ChipInterface : chip_name -> inputs -> outputs -> chip_interface.

Inductive chip : Set :=
| BuiltIn : forall (i : chip_interface), chip
| Composite : forall (i : chip_interface), parts -> chip.


Module HDLNotations.
  (* TODO: verify levels are reasonable *)

  Notation "'IN' in1 , .. , inn" :=
    (Inputs (cons (Pin in1)
                  ..
                  (cons (Pin inn) nil) ..))
      (at level 0) : HDL_scope.

  Notation "'OUT' out1 , .. , outn" :=
    (Outputs (cons (Pin out1)
                   ..
                   (cons (Pin outn) nil) ..))
      (at level 0) : HDL_scope.

  Notation "x -- y" :=
    (Connection x y)
      (at level 0, no associativity) : HDL_scope.

  Notation "x -- -" :=
    (ConstSignal x false)
      (at level 0, no associativity) : HDL_scope.

  Notation "x -- +" :=
    (ConstSignal x true)
      (at level 0, no associativity) : HDL_scope.

  Notation "'_' name {{ conn1 , .. , connn }}" :=
    (InternalChip name
                  (Connections
                     (cons conn1
                           ..
                           (cons connn nil) ..)))
      (at level 0) : HDL_scope.

  Notation "'PARTS:' part1 ; .. ; partn" :=
    (Parts (cons part1
                 ..
                 (cons partn nil) ..))
      (at level 0) : HDL_scope.

  Notation "'BUILTIN' name {{ inputs ; outputs ; }}" :=
    (BuiltIn (ChipInterface name inputs outputs)) : HDL_scope.

  Notation "'CHIP' name {{ inputs ; outputs ; parts }}" :=
    (Composite (ChipInterface name inputs outputs) parts) : HDL_scope.

End HDLNotations.
Import HDLNotations.

Open Scope HDL_scope.

Check IN "a", "b".
Check OUT "out".
Check _"NAND" {{ "a" -- "x", "b" -- "y", "out" -- "c0" }}.
Check BUILTIN "NAND" {{
                         IN "a", "b";
                         OUT "out";
                       }}.
Check PARTS:
  _"P1" {{ "a" -- "x", "b" -- "y", "out" -- "c0" }};
  _"P2" {{ "a" -- "c0", "b" -- "y", "out" -- "out" }}.

Check CHIP "XYZ" {{
                     IN "p", "q", "r";
                     OUT "out1", "out2";
                     PARTS:
                       _"CHIP1" {{
                                    "x" -- "p",
                                    "out" -- "c0"
                                  }};
                       _"CHIP2" {{
                                    "x" -- "q",
                                    "y" -- "c0",
                                    "out" -- "out1"
                                  }};
                       _"CHIP3" {{
                                    "a" -- "c0",
                                    "out" -- "out"
                                  }}
                   }}.

Definition chip_registry : Type := list chip.

Definition name_of (chip : chip) : chip_name :=
  match chip with
    | BUILTIN n {{ _ ; _  ; }} => n
    | CHIP n {{ _ ; _ ; _ }} => n
  end.

Fixpoint get_chip (name : chip_name) (chips : list chip) : option chip :=
  find (fun c => if string_dec (name_of c) name then true else false) chips.



Definition nand_gate : chip :=
  BUILTIN "NAND" {{
                     IN "a", "b";
                     OUT "out";
                   }}.

Definition not_gate : chip :=
  CHIP "NOT" {{
                 IN "in";
                 OUT "out";
                 PARTS:
                   _"NAND" {{ "a" -- "in",
                              "b" -- "in",
                              "out" -- "out" }}
                    }}.

Definition and_gate : chip :=
  CHIP "AND" {{
                 IN "a", "b";
                 OUT "out";
                 PARTS:
                   _"NAND" {{ "a" -- "a",
                              "b" -- "b",
                              "out" -- "c0" }};
                   _"NOT" {{ "in" -- "c0",
                             "out" -- "out" }}
               }}.

Definition or_gate : chip :=
  CHIP "OR" {{
                IN "a", "b";
                OUT "out";
                PARTS:
                  _"NAND" {{ "a" -- +,
                             "b" -- "a",
                             "out" -- "c0" }};
                  _"NAND" {{ "a" -- +,
                             "b" -- "b",
                             "out" -- "c1" }};
                  _"NAND" {{ "a" -- "c0",
                             "b" -- "c1",
                             "out" -- "out" }}
                   }}.

Definition nor_gate : chip :=
  CHIP "NOR" {{
                 IN "a", "b";
                 OUT "out";
                 PARTS:
                   _"OR" {{ "a" -- "a",
                            "b" -- "b",
                            "out" -- "c0" }};
                   _"NOT" {{ "in" -- "c0",
                             "out" -- "out" }}
               }}.

Definition xor_gate : chip :=
  CHIP "XOR" {{
                 IN "a", "b";
                 OUT "out";
                 PARTS:
                   _"NAND" {{ "a" -- "a",
                              "b" -- "b",
                              "out" -- "c0" }};
                   _"NOT" {{ "in" -- "a",
                             "out" -- "a0" }};
                   _"NOT" {{ "in" -- "b",
                             "out" -- "b0" }};
                   _"NAND" {{ "a" -- "a0",
                              "b" -- "b0",
                              "out" -- "c1" }};
                   _"AND" {{ "a" -- "c0",
                             "b" -- "c1",
                             "out" -- "out" }}
               }}.

Definition provisional_registry : chip_registry :=
  [ nand_gate;
    not_gate;
    and_gate;
    or_gate;
    nor_gate;
    xor_gate ].

(* TODO: make a truth table type with [n] bool inputs with [m] outputs *)
(* TODO: define the truth table for the builtin NAND chip *)
(* TODO: derive truth tables for the other chips and prove they are as expected *)


(* TODO:

   - [ ] model an environment of chips, each identified by name
     - see Registry.v for humble beginnings of unique-key enforced association lists
     - NB: while important, focusing too much on correctness by construction in the first iteration won't get me anywhere
   - [ ] make chips correct by construction
     - [ ] a part must be a chip recognized in the environment.
     - [ ] a chip introduced to the environment must have a unique name.
     - [ ] the LHS of a part's connections must be valid pins for that part.
     - [ ] the RHS of a part's connections must be valid pins for the chip.
     - [ ] an input pin is fed in by an input pin of the chip, an internal pin, true, or false.
     - [ ] an output pin is fed in by an output pin of the chip or an internal pin.
   - [ ] support bus pins and subrange notation
   - [ ] support sequential chips (A.7)
   - [ ] test scripting language (B)
   - [ ] hardware simulator

 *)
