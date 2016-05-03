Require Import List.
Open Scope type_scope.
Import ListNotations.

Definition assoc_list K V : Type := list (K * V).

Fixpoint assoc_keys {K V : Type} (al : assoc_list K V) : list K :=
  match al with
    | [] => []
    | (k, _) :: al' => k :: assoc_keys al'
  end.

Definition eq_for (T : Type) : Type := forall (a b : T), {a = b}+{a <> b}.

Fixpoint member {T : Type} (x : T) (xs : list T) {eq_dec : eq_for T} : Prop :=
  match xs with
    | [] => False
    | (x' :: xs') => if eq_dec x' x then True else @member _ x xs' eq_dec
  end.

Inductive assoc_uniq {K V : Type} (eq_dec : eq_for K) : assoc_list K V -> Prop :=
| AssocUniqNil : assoc_uniq eq_dec []
| AssocUniqCons : forall (k : K) (v : V) (al : assoc_list K V),
                    ~ @member _ k (assoc_keys al) eq_dec -> assoc_uniq eq_dec ((k,v) :: al).

Lemma empty_is_uniq : forall (K V : Type) (eq_dec : _), @assoc_uniq K V eq_dec [].
Proof.
  intros K V eq_dec.
  apply AssocUniqNil.
Qed.

Lemma singleton_is_uniq : forall (K V : Type) (pair : (K * V)) (eq_dec : _), assoc_uniq eq_dec [pair].
Proof.
  intros K V pair eq_dec.
  destruct pair.
  apply AssocUniqCons.
  simpl.
  apply neg_false.
  apply iff_refl.
Qed.

Inductive registry K V (eq_dec : eq_for K): Type :=
| Registry : forall (al : assoc_list K V) {p : assoc_uniq eq_dec al}, registry K V eq_dec.

(* TODO: examples of using [registry]. refactor as needed to simplify *)




(* Experiments with Coq built-in map interfaces *)


(* http://stackoverflow.com/questions/14489232/finite-map-example *)
Require Import FMapAVL.
Require Import OrderedTypeEx.

Module M := FMapAVL.Make(Nat_as_OT).

Definition map_nat_nat : Type := M.t nat.

Definition find k (m : map_nat_nat) := M.find k m.

Definition update (p : nat * nat) (m : map_nat_nat) :=
  M.add (fst p) (snd p) m.

Notation "k |-> v" := (pair k v) (at level 60, no associativity).
Notation "[ ]" := nil.
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty nat))..).

Example ex1 : find 3 [1 |-> 2, 3 |-> 4] = Some 4.
Proof. reflexivity. Qed.

Example ex2 : find 5 [1 |-> 2, 3 |-> 4] = None.
Proof. reflexivity. Qed.

Example ex3 : find 0 [0 |-> 1, 0 |-> 2] = Some 1.
Proof. reflexivity. Qed.