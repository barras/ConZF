From Stdlib Require Export
  Setoid Morphisms Morphisms_Prop.

(*
Sets as trees (Aczel), from scratch in Lean core, so that `#print axioms` shows exactly what
is used. Nothing here uses `Classical.choice`.
*)

Lemma fa_morph A P P' :
  (forall x, P x <-> P' x) ->
  (forall x:A, P x) <-> (forall x:A, P' x).
split; intros; apply H; trivial.
Qed.
Lemma ex_morph A P P' :
  (forall x, P x <-> P' x) ->
  (exists x:A, P x) <-> (exists x:A, P' x).
split; intros (x,p); exists x; apply H; trivial.
Qed.
Lemma impl_morph P P' Q Q' :
  (P <-> P') ->
  (P -> Q <-> Q') ->
  (P -> Q) <-> (P' -> Q').
split; intros; apply H in H2; apply H0; auto.
apply H; trivial.
Qed.




(*- `V = W X : Type u. X`. *)
Inductive PSet : Type :=
  | mk (α : Type) (A : α -> PSet) : PSet.

Definition Idx (x:PSet) : Type :=
  let (α, _) := x in α.
Definition Func (x : PSet) : Idx x -> PSet :=
  match x with
  | mk _ A => A
  end.

Lemma mk_eta (x : PSet) : x = mk (Idx x) (Func x).
  destruct x; reflexivity.
Qed.

(*- Bisimulation. *)
Fixpoint Equiv (x y: PSet) : Prop :=
  match x, y with
  | mk _ A, mk _ B => (forall a, exists b, Equiv (A a) (B b)) /\ (forall b, exists a, Equiv (A a) (B b))
  end.

Infix "≈" := Equiv (at level 50, left associativity).


Lemma Equiv_refl (x : PSet) : x ≈ x.
revert x; fix rfl 1.
destruct x as (A,F); simpl.
split; intros y; exists y; apply rfl.
Qed.

Lemma Equiv_symm {x y : PSet} : x ≈ y -> y ≈ x.
revert x y; fix symm 1; intros (A,F) (B,G); simpl.
destruct 1 as (h1,h2); split; intros i;
  [destruct (h2 i) as (j,e)|destruct (h1 i) as (j,e)]; exists j;
  apply symm; assumption.
Qed.

Lemma Equiv_trans {x y z : PSet} : x ≈ y -> y ≈ z -> x ≈ z.
revert x y z; fix trans 1; intros (A,F) (B,G) (C,H); simpl.
intros (h1,h2) (h1',h2'); split; intros i;
  [destruct (h1 i) as (j,e); destruct (h1' j) as (k,e')
  |destruct (h2' i) as (j,e); destruct (h2 j) as (k,e')];
  exists k; apply trans with (G j); assumption.
Qed.

Definition Mem (x y : PSet) : Prop := exists b, x ≈ Func y b.

(*instance : Membership PSet PSet := ⟨fun y x => Mem x y⟩*)
Infix "∈" := Mem (at level 50).
  
Lemma mem_def {x y : PSet} : x ∈ y <-> exists b, x ≈ Func y b.
  reflexivity.
Qed.

Lemma func_mem (y : PSet) (b : Idx y) : Func y b ∈ y.
  exists b; apply Equiv_refl.
Qed.

Lemma mem_congr_left {x x' y : PSet} (h : x ≈ x') : x ∈ y <-> x' ∈ y.
split; destruct 1 as (b,e); exists b; apply Equiv_trans with (2:=e);
  [apply Equiv_symm|]; trivial.
Qed.

Lemma equiv_iff_mem {x y : PSet} : x ≈ y <-> (forall z, z ∈ x <-> z ∈ y).
destruct x as (A,F); destruct y as (B,G); simpl.
split.
*intros (h1,h2) z.
 split; intros (i,e); simpl in e;
   [destruct (h1 i) as (j,h)|destruct (h2 i) as (j,h)]; exists j; simpl.
 +apply Equiv_trans with (1:=e); trivial.
 +apply Equiv_trans with (1:=e); apply Equiv_symm; trivial.
*intros eqv; split; intros i;
   [destruct (proj1 (eqv (F i)) (ex_intro _ i (Equiv_refl (F i)))) as (j,e)
   |destruct (proj2 (eqv (G i)) (ex_intro _ i (Equiv_refl (G i)))) as (j,e)];
   exists j; [|apply Equiv_symm]; trivial.
Qed.

Lemma ext {x y : PSet} (H : forall z, z ∈ x <-> z ∈ y) : x ≈ y.
apply equiv_iff_mem; trivial.
Qed.

Lemma mem_congr_right {x y y' : PSet} (h : y ≈ y') : x ∈ y <-> x ∈ y'.
  apply equiv_iff_mem; trivial.
Qed.

(*- `∈`-induction, for predicates that need not respect `≈`. *)
Lemma mem_induction {P : PSet -> Prop}
  (H : forall x, (forall y, y ∈ x -> P y) -> P x) (x : PSet) : P x.
assert (suf : forall x y, y ≈ x -> P y);
  [clear x|apply suf with x; apply Equiv_refl].
induction x; intros y hy.
apply H; intros z hz.
destruct (proj1 (mem_congr_right hy) hz) as (i,e).
apply (H0 i); trivial.
Qed.

(*! ### Operations *)

Definition empty : PSet := mk False (fun i => match i with end).

Lemma not_mem_empty (x : PSet) : ~ x ∈ empty.
  intros (b, _); exact b.
Qed.

(*- The set `{A i | i : ι}` of a family indexed by a small type. *)
Definition range {ι : Type} (A : ι -> PSet) : PSet :=  mk ι A.

Lemma mem_range {ι : Type} {A : ι -> PSet} {x} :
  x ∈ range A <-> exists i, x ≈ A i.
  reflexivity.
Qed.

Definition sUnion (a : PSet) : PSet :=
  mk {x : Idx a & Idx(Func a x)}
    (fun p => Func (Func a (projT1 p)) (projT2 p)).

Lemma mem_sUnion {a x : PSet} :
  x ∈ sUnion a <-> exists y, y ∈ a /\ x ∈ y.
split.
*intros ((i, j), e); simpl in *.
 exists (Func a i); split; [exists i; apply Equiv_refl|].
 exists j; trivial.
*intros  (y & (i, e) & hx).
 destruct (proj1 (mem_congr_right e) hx) as (j, e').
 exists (existT _ i j); simpl; trivial.
Qed.

(*- `⋃ i, A i` for a family indexed by a small type. *)
Definition iUnion {ι : Type} (A : ι -> PSet) : PSet := sUnion (range A).

Lemma mem_iUnion {ι : Type} {A : ι -> PSet} {x} :
  x ∈ iUnion A <-> exists i, x ∈ A i.
unfold iUnion.
rewrite mem_sUnion.
split.
*intros (y & (a,hy) & hx); simpl in a; exists a.
 apply mem_congr_right with (1:=hy); trivial.
*intros (i, hx); exists (A i); split; [|trivial].
 exists i; apply Equiv_refl.
Qed.

(*- The union of a family indexed by the proofs of a proposition: `t` if `P` holds, `∅` if not.
This is what replaces a decision procedure for `P`. *)
Definition guard (P : Prop) (t : P -> PSet) : PSet :=
  iUnion (ι := P) (fun h => t h).

Lemma mem_guard {P : Prop} {t : P -> PSet} {x} :
  x ∈ guard P t <-> exists h : P, x ∈ t h.
unfold guard; rewrite mem_iUnion; reflexivity.
Qed.

Definition union (a b : PSet) : PSet :=
  iUnion (ι := bool) (fun i => if i then a else b).

Lemma mem_union {a b x : PSet} : x ∈ union a b <-> x ∈ a \/ x ∈ b.
unfold union; rewrite mem_iUnion; split.
*intros ([|],h); auto.
*intros [h|h]; [exists true|exists false]; trivial.
Qed.

Definition singleton (a : PSet) : PSet := range (ι := unit) (fun _ => a).

Lemma mem_singleton {a x : PSet} : x ∈ singleton a <-> x ≈ a.
split.
*intros (?,h); trivial.
*exists tt; trivial.
Qed. 

Definition succ (a : PSet) : PSet := union a (singleton a).

Lemma mem_succ {a x : PSet} : x ∈ succ a <-> x ∈ a \/ x ≈ a.
unfold succ; rewrite mem_union.
apply or_iff_morphism; [reflexivity|apply mem_singleton].
Qed.

Lemma mem_succ_congr {a a' x : PSet} (h : a ≈ a') :
  x ∈ succ a <-> x ∈ succ a'.
rewrite !mem_succ.
apply or_iff_morphism; [apply mem_congr_right with (1:=h)|].
split; intros; eauto using Equiv_trans, Equiv_symm.
Qed.

(*- Separation. *)
Definition sep (p : PSet -> Prop) (a : PSet) : PSet :=
  range (ι := {i : Idx a | p (Func a i)}) (fun i => Func a (proj1_sig i)).

Lemma mem_sep {p : PSet -> Prop} (hp : forall x y, x ≈ y -> p x -> p y) {a x : PSet} :
  x ∈ sep p a <-> x ∈ a /\ p x.
split.
*intros ((i,h),e); simpl in e; split; [exists i;trivial|].
 revert h; apply hp; apply Equiv_symm; trivial.
*intros ((i,e),h); exists (exist (fun i => p (Func a i)) i (hp _ _ e h)); trivial.
Qed.
