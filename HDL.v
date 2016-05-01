Require Import String.
Require Import List.

Open Scope string_scope.
Import ListNotations.


Definition chip_name : Set := string.
Definition pin_name : Set := string.

Inductive connection : Set :=
| Connection : pin_name -> pin_name -> connection.

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

Definition interface_name (i : chip_interface) : chip_name :=
  match i with
    | ChipInterface n _ _ => n
  end.

Inductive chip : chip_name -> Set :=
| BuiltIn : forall (i : chip_interface), chip (interface_name i)
| Composite : forall (i : chip_interface), parts -> chip (interface_name i).


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

(* TODO:

   - [ ] model an environment of chips, each identified by name
     - see Registry.v for humble beginnings of unique-key enforced association lists
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
