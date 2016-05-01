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