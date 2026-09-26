Require Import Repl.
(*import ConZF.NatInstance*)
(*!
Ordinals and rank. Excluded middle, where needed, is an explicit hypothesis
`em : forall p : Prop, p \/ ¬p`, never `Classical.em` (which is proved from choice).
*)
Import PSet.

Definition Trans (t : PSet) : Prop := forall y, y ∈ t -> forall z, z ∈ y -> z ∈ t.

(*- Von Neumann ordinals: transitive sets of transitive sets (foundation is built in). *)
Class IsOrd (t : PSet) : Prop := {
    IsOrd_trans : Trans t;
    IsOrd_mem_trans : forall y, y ∈ t -> Trans y
  }.

Lemma Trans_resp {t t' : PSet} (e : t ≈ t') (h : Trans t) : Trans t'.
intros y hy z hz.
apply mem_congr_right with (1:=e).
apply h with y; trivial.
apply mem_congr_right with (1:=e); trivial.
Qed.

Lemma IsOrd_resp {t t' : PSet} (e : t ≈ t') (h : IsOrd t) : IsOrd t'.
destruct h as (h1,h2).
split.
*revert h1; apply Trans_resp; trivial.
*intros; apply h2.
 apply mem_congr_right with (1:=e); trivial.
Qed.

Lemma IsOrd_mem {t y : PSet} (h : IsOrd t) (hy : y ∈ t) : IsOrd y.
destruct h as (h1,h2).
split; [auto|].
intros.
apply h2.
revert H; apply h1; trivial.
Qed.

Lemma isOrd_empty : IsOrd empty.
split; red; intros.
*apply not_mem_empty in H; contradiction.
*apply not_mem_empty in H; contradiction.
Qed.

Instance IsOrd_succ {t : PSet} (h : IsOrd t) : IsOrd (succ t).
destruct h as (h1,h2).
split.
*intros y hy z hz.
 apply mem_succ; left.
 apply mem_succ in hy; destruct hy.
 +revert hz; apply h1; trivial.
 +apply mem_congr_right with (1:=H); trivial.
*intros y hy.
 apply mem_succ in hy; destruct hy as [hy | e]; [auto|].
 revert h1; apply Trans_resp.
apply Equiv_symm; trivial.
Qed.

Instance isOrd_iUnion {ι : Type} {A : ι -> PSet} (h : forall i, IsOrd (A i)) : IsOrd (iUnion A).
split.
*intros y hy z hz.
 rewrite mem_iUnion in hy; destruct hy as (i, hi).
 apply mem_iUnion; exists i.
 revert hz; apply IsOrd_trans; trivial.
*intros y hy.
 rewrite mem_iUnion in hy; destruct hy as (i, hi).
 eapply IsOrd_mem_trans; eassumption.
Qed.

Lemma not_mem_self (a : PSet) : ~ a ∈ a.
intros h.
apply (@mem_asymm a a); trivial.
Qed.

Section em.
Hypothesis (em : forall p : Prop, p \/ ~p).

(*- Ordinals are linearly ordered by `∈`. *)
Lemma IsOrd_trichotomy : forall {a b : PSet}, IsOrd a -> IsOrd b -> a ∈ b \/ a ≈ b \/ b ∈ a.
intros a.
induction a using @mem_induction; rename H into iha.
intros b.
induction b using @mem_induction; rename H into ihb.
intros ha hb.
destruct (em (a ∈ b)) as [h1 | h1].
*left; trivial.
*destruct (em (b ∈ a)) as [h2 | h2].
 **right; right; trivial.
 **right; left.
   apply ext; intros z; split; intros hz.
   +destruct iha with z b as [h|[h|h]];
      trivial; [apply IsOrd_mem with (2:=hz); trivial| |].
    ++elim h2; apply mem_congr_left with (1:=h); trivial.
    ++elim h2; revert h; apply IsOrd_trans; trivial.
   +destruct ihb with z as [h|[h|h]];
      trivial; [apply IsOrd_mem with (2:=hz); trivial| |].
    ++elim h1; revert h; apply IsOrd_trans; trivial.
    ++elim h1; apply mem_congr_left with (1:=h); trivial.
Qed.

(*- For ordinals, inclusion is `∈` or `≈`. *)
Lemma IsOrd_subset {a b : PSet} (ha : IsOrd a) (hb : IsOrd b) (h : forall z, z ∈ a -> z ∈ b) :
  a ∈ b \/ a ≈ b.
destruct (IsOrd_trichotomy ha hb) as [h' |[ h' | h']]; auto.
destruct (not_mem_self b (h b h')).
Qed.

End em.

(*! ### Rank *)

Fixpoint rank (x:PSet) : PSet :=
  iUnion (fun a:Idx x => succ (rank (Func x a))).

Lemma mem_rank {x z : PSet} : z ∈ rank x <-> exists a, z ∈ succ (rank (Func x a)).
destruct x; exact mem_iUnion.
Qed.

Lemma rank_congr : forall {x y : PSet}, x ≈ y -> rank x ≈ rank y.
fix hrec 1; intros (A,F) (B,G) (h1,h2).
apply ext; intros z.
rewrite !mem_rank.
simpl.
split.
*intros (a,h); destruct (h1 a) as (b,e).
 exists b.
 revert h; apply (fun e=>proj1(mem_succ_congr e)).
 apply hrec; trivial.
*intros (b,h); destruct (h2 b) as (a,e).
 exists a.
 revert h; apply (fun e=>proj2(mem_succ_congr e)).
 apply hrec; trivial.
Qed.

Lemma rank_mem {x y : PSet} (h : y ∈ x) : rank y ∈ rank x.
destruct h as (a,e).
rewrite mem_rank.
exists a.
rewrite mem_succ; right.
apply rank_congr; trivial.
Qed.

Lemma isOrd_rank : forall x : PSet, IsOrd (rank x).
fix isOrd 1; intros (A,F); simpl.
apply isOrd_iUnion; intros a.
apply IsOrd_succ; apply isOrd.
Qed.
