Require Import Ord Pair.
(*!
Power set, the levels `V_x` (for any set `x`, of rank `rank x`), finite ordinals and `ω`, and the
label set `D G = V_{G+ω}` of the definability rule, all characterized through ranks.
*)

Import PSet.

(*- Power set: subsets are indexed by predicates on the index type, which is small because
`Prop` is impredicative. *)
Definition powerset (X : PSet) : PSet :=
  range (ι := Idx X -> Prop) (fun S => range (ι := {i | S i}) (fun i => Func X (proj1_sig i))).

Lemma mem_powerset {X y : PSet} : y ∈ powerset X <-> forall z, z ∈ y -> z ∈ X.
split.
*Tintros (S, e); intros z hz.
 apply mem_congr_right with (1:=e) in hz.
 Tdestruct hz as ((i,?),e').
 simpl in e'. 
 Texists i; trivial.
*intros h.
 Texists (fun i => Func X i ∈ y).
 apply ext; intros z.
 split.
 +intros hz.
  Tdestruct (h z hz) as (i,e').
  apply mem_congr_left with (1:=e') in hz.
  Texists (exist (fun _=>_) i hz); simpl; trivial.
 +Tintros ((i, hi), e'); simpl in e'.
  apply mem_congr_left with (1:=e'); trivial.
Qed.

(*- `z ∈ rank x` iff `z ≤ rank y` for some `y ∈ x`. *)
Lemma mem_rank' {x z : PSet} : z ∈ rank x <-> #exists y, y ∈ x /\ z ∈ succ (rank y).
rewrite mem_rank.
split.
*Tintros (a,h); apply TrI;eexists; split; [eapply func_mem|eassumption].
*Tintros (y & m(*(a,e)*) & h); Tdestruct m as (a,e); Texists a.
 revert h; apply mem_succ_congr; apply Equiv_symm.
 apply rank_congr; trivial. 
Qed.

Lemma succ_congr {a a' : PSet} (h : a ≈ a') : succ a ≈ succ a'.
apply ext; intros z.
apply mem_succ_congr; trivial.
Qed.

(*- The rank of an ordinal is itself. *)
Lemma IsOrd_rank_equiv : forall {t : PSet}, IsOrd t -> rank t ≈ t.
intros t; elim t using @mem_induction; [auto|clear t; intros t ih].
intros ht; apply ext; intros z.
rewrite mem_rank'.
split.
*Tintros (y & hy& hz).
 assert (ey : rank y ≈ y).
 {apply ih; trivial.
  apply IsOrd_mem with (2:=hy); trivial. }
 rewrite mem_succ_congr with (1:=ey) in hz.
 apply mem_succ in hz; Tdestruct hz as [hz|e].
 +revert hz; apply IsOrd_trans; trivial.
 +apply mem_congr_left with (1:=e); trivial.
*intros hz; Texists z; split; trivial.
 assert (ez : rank z ≈ z).
 {apply ih; trivial.
  apply IsOrd_mem with (2:=hz); trivial. }
 rewrite mem_succ_congr with (1:=ez).
 rewrite mem_succ; Tright; apply Equiv_refl.
Qed.

Section em.
Hypothesis (em : forall p : Prop, #(p \/ ~p)).

(*- If every element of `y` has rank below the ordinal `R`, then `rank y ≤ R`. *)
Lemma rank_mem_succ {y R : PSet} (hR : IsOrd R) (h : forall z, z ∈ y -> rank z ∈ R) :
    rank y ∈ succ R.
rewrite mem_succ.
apply (IsOrd_subset em); [apply isOrd_rank|trivial|].
intros w hw.
apply mem_rank' in hw.
Tdestruct hw as (z& hz& hw).
apply mem_succ in hw; Tdestruct hw as [hw|e].
*apply IsOrd_trans with (2:=hw); auto.
*apply mem_congr_left with (1:=e); auto.
Qed.

Lemma rank_singleton_mem {a R : PSet} (hR : IsOrd R) (ha : rank a ∈ R) :
    rank (singleton a) ∈ succ R.
apply rank_mem_succ; trivial.
intros ? hz.
apply mem_singleton in hz.
revert ha; apply mem_congr_left.
apply rank_congr; trivial.
Qed.

Lemma rank_upair_mem {a b R : PSet} (hR : IsOrd R) (ha : rank a ∈ R) (hb : rank b ∈ R) :
    rank (upair a b) ∈ succ R.
apply rank_mem_succ; trivial.
intros z hz.
apply mem_upair in hz.
Tdestruct hz as [e|e].
*revert ha;apply mem_congr_left; apply rank_congr; trivial.
*revert hb;apply mem_congr_left; apply rank_congr; trivial.
Qed.

Lemma rank_pair_mem {a b R : PSet} (hR : IsOrd R) (ha : rank a ∈ R) (hb : rank b ∈ R) :
    rank (pair a b) ∈ succ (succ R).
apply rank_upair_mem.
*apply IsOrd_succ; trivial.
*apply rank_singleton_mem; trivial.
*apply rank_upair_mem; trivial.
Qed.

Lemma rank_triple_mem {a b c R : PSet} (hR : IsOrd R)
    (ha : rank a ∈ R) (hb : rank b ∈ R) (hc : rank c ∈ R) :
    rank (triple a b c) ∈ succ (succ (succ (succ R))).
apply rank_pair_mem.
*do 2apply IsOrd_succ; trivial.
*do 2 (rewrite mem_succ; Tleft); trivial.
*apply rank_pair_mem; trivial.
Qed.

End em.

(*! ### Levels *)

(*- `Vl x` is the set of sets of rank below `rank x`. *)
Fixpoint Vl (x:PSet) : PSet :=
  iUnion (fun a => powerset (Vl (Func x a))).

Lemma mem_Vl (em : forall p : Prop, #(p \/ ~p)) : forall {x y : PSet}, y ∈ Vl x <-> rank y ∈ rank x.
fix mem_Vl 1.
intros (A,F) y.
simpl Vl.
rewrite mem_iUnion, mem_rank.
apply Tr_morph; apply ex_morph; intros a.
rewrite mem_powerset.
split.
*intros h.
 apply (rank_mem_succ em); [apply isOrd_rank|].
 intros z hz.
 rewrite <- mem_Vl; auto.
*intros h z hz.
 simpl in h.
 rewrite mem_Vl.
 apply rank_mem in hz.
 rewrite mem_succ in h.
 Tdestruct h as [h|e]. 
 +assert (h1 := isOrd_rank (F a)).
  revert hz; apply (IsOrd_trans _); trivial.
 +apply mem_congr_right with (1:=e); trivial.
Qed.

(*! ### Finite ordinals and `ω` *)

Fixpoint ofNat (n : nat) : PSet :=
  match n with
  | 0 => empty
  | S n => succ (ofNat n)
  end.

Lemma isOrd_ofNat : forall n, IsOrd (ofNat n).
  induction n; [apply isOrd_empty|simpl;apply IsOrd_succ; trivial].  
Qed.

Definition omega : PSet :=
  range (ι := nat) (fun n => ofNat n).

Lemma mem_omega {x : PSet} : x ∈ omega <-> #exists n, x ≈ ofNat n.
apply mem_range.
Qed.

Lemma isOrd_omega : IsOrd omega.
split.
*intros y hy z hz.
 rewrite mem_omega in hy.
 Tdestruct hy as (n,e).
 apply mem_congr_right with (1:=e) in hz.
 clear -hz.
 revert z hz; induction n; simpl ofNat; intros.
 +apply not_mem_empty in hz; contradiction.
 +rewrite mem_succ in hz; Tdestruct hz as [h|e']; auto.
  apply mem_omega; Texists n; trivial.
*intros y hy.
 rewrite mem_omega in hy; Tdestruct hy as (n,e).
 apply Trans_resp with (1:=Equiv_symm e).
 apply isOrd_ofNat.
Qed.

(*! ### The label set *)

Fixpoint succN (n:nat) (G:PSet) : PSet :=
  match n with
  | 0 => G
  | S n => succ (succN n G)
  end.

(*- `D G = V_{rank G + ω}`. *)
Definition D (G : PSet) : PSet :=
  iUnion (ι := nat) (fun n => Vl (succN n G)).

Lemma mem_D (em : forall p : Prop, #(p \/ ~p)) {G y : PSet} :
    y ∈ D G <-> #exists n, rank y ∈ rank (succN n G).
unfold D; rewrite mem_iUnion.
apply Tr_morph; apply ex_morph; intros n.
apply (mem_Vl em).
Qed.

Lemma IsOrd_iterate_succ {G : PSet} (h : IsOrd G) : forall n, IsOrd (succN n G).
induction n; simpl succN; trivial.
apply IsOrd_succ; trivial.
Qed.

(*- For an ordinal `G`, a set whose rank is below `G + n` is in `D G`. *)
Lemma mem_D_of_rank (em : forall p : Prop, #(p \/ ~p)) {G y : PSet} (hG : IsOrd G) (n : nat)
    (h : rank y ∈ succN n G) : y ∈ D G.
apply (mem_D em).
Texists n.
assert (hGn := IsOrd_iterate_succ hG n). 
apply IsOrd_rank_equiv in hGn.
apply mem_congr_right with (1:=hGn); trivial.
Qed.
