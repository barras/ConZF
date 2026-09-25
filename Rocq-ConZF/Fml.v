From Stdlib Require Import Arith.
Require Import PSet Pair VLevel Worldly NatInstance.
(*!
First-order formulas of set theory with de Bruijn variables, satisfaction in a class model
`M : PSet -> Prop` (quantifiers range over `M`), renaming of variables, bounds on the free
variables, and an injective coding of formulas as sets (used to put a formula into a label).
*)
Lemma fa_morph A P P' :
  (forall x, P x <-> P' x) ->
  (forall x:A, P x) <-> (forall x:A, P' x).
split; intros; apply H; trivial.
Qed.
Lemma impl_morph P P' Q Q' :
  (P <-> P') ->
  (P -> Q <-> Q') ->
  (P -> Q) <-> (P' -> Q').
split; intros; apply H in H2; apply H0; auto.
apply H; trivial.
Qed.


Inductive Fml : Set :=
  | mem (i j : nat)
  | eq (i j : nat)
  | fls
  | imp (φ ψ : Fml)
  | all (φ : Fml).

Definition neg (φ : Fml) : Fml := imp φ fls.
Definition and (φ ψ : Fml) : Fml := neg (imp φ (neg ψ)).
Definition or (φ ψ : Fml) : Fml := imp (neg φ) ψ.
Definition iff (φ ψ : Fml) : Fml := and (imp φ ψ) (imp ψ φ).
Definition ex (φ : Fml) : Fml := neg (all (neg φ)).

(*- Lifting a renaming under a binder. *)
Definition up (ρ : nat -> nat) (k : nat) : nat :=
  match k with
  | 0 => 0
  | S n => S (ρ n)
  end.

Fixpoint rename (ρ : nat -> nat) (f : Fml) : Fml :=
  match f with
  | mem i j => mem (ρ i) (ρ j)
  | eq i j => eq (ρ i) (ρ j)
  | fls => fls
  | imp φ ψ => imp (rename ρ φ) (rename ρ ψ)
  | all φ => all (rename (up ρ) φ)
  end.

(*- Substitution of the variable `j` for the bound variable `0`. *)
Definition inst (j : nat) (k : nat) : nat :=
  match k with
  | 0 => j
  | S n => n
  end.

Definition lift (φ : Fml) : Fml := rename S φ.

(*- All free variables of `φ` are below `k`. *)
Fixpoint Bound (k : nat) (f : Fml) : Prop :=
  match f with
  | mem i j => i < k /\ j < k
  | eq i j => i < k /\ j < k
  | fls => True
  | imp φ ψ => Bound k φ /\ Bound k ψ
  | all φ => Bound (S k) φ
  end.

Lemma Bound_mono : forall {φ : Fml} {k k' : nat}, k <= k' -> Bound k φ -> Bound k' φ.
induction φ; simpl; try destruct 2; eauto with arith.
Qed.

Lemma le_nmax_left : forall a b, a <= max a b.
apply Nat.le_max_l.
Qed.

Lemma le_nmax_right : forall a b, b <= max a b.
apply Nat.le_max_r.
Qed.

Lemma exists_bound : forall φ : Fml, exists k, Bound k φ.
induction φ; simpl. 
*exists (S (max i j)); split; auto with arith.
*exists (S (max i j)); split; auto with arith.
*exists 0; trivial.
*destruct IHφ1 as (a,ha); destruct IHφ2 as (b,hb).
 exists (max a b); split; (eapply Bound_mono;[|eassumption]); eauto with arith.
*destruct IHφ as (a,ha).
 exists a; eapply Bound_mono;[|eassumption]; auto with arith.
Qed.

Definition Env_cons (x : PSet) (e : nat -> PSet) (k : nat) : PSet :=
  match k with
  | 0 => x
  | S n => e n
  end.

(*- Satisfaction in the class model `M`. *)
Fixpoint Sat (M : PSet -> Prop) (f : Fml) (e : nat -> PSet) : Prop :=
  match f with
  | mem i j => e i ∈ e j
  | eq i j => e i ≈ e j
  | fls => False
  | imp φ ψ => Sat M φ e -> Sat M ψ e
  | all φ => forall x, M x -> Sat M φ (Env_cons x e)
  end.

Lemma Env_cons_resp {x x' : PSet} {e e' : nat -> PSet} (hx : x ≈ x')
    (he : forall i, e i ≈ e' i) : forall i, Env_cons x e i ≈ Env_cons x' e' i.
destruct i; simpl; auto.
Qed.

Lemma Sat_resp_iff {M M' : PSet -> Prop} (hM : forall x, M x <-> M' x) :
  forall (φ : Fml) {e e' : nat -> PSet}, (forall i, e i ≈ e' i) ->
                                         (Sat M φ e <-> Sat M' φ e').
induction φ; simpl; intros.
*eapply transitivity; [eapply mem_congr_left|eapply mem_congr_right]; trivial.
*split; intros.
 +eapply Equiv_trans; [apply Equiv_symm; apply H|].
  eapply Equiv_trans; [|apply H]; trivial.
 +eapply Equiv_trans; [apply H|].
  eapply Equiv_trans; [|apply Equiv_symm; apply H]; trivial.
*reflexivity.
*apply impl_morph; auto.
*apply fa_morph; intros x.
 apply impl_morph; [trivial|intro].
 apply IHφ; intros; apply Env_cons_resp; [apply Equiv_refl|trivial].
Qed.

Lemma Sat_resp {M : PSet -> Prop} (φ : Fml) {e e' : nat -> PSet}
    (h : forall i, e i ≈ e' i) (s : Sat M φ e) : Sat M φ e'.
revert s; apply Sat_resp_iff; [reflexivity|intros; apply Equiv_symm;trivial].
Qed.

Lemma sat_rename {M : PSet -> Prop} :
    forall (φ : Fml) (ρ : nat -> nat) (e : nat -> PSet),
      Sat M (rename ρ φ) e <-> Sat M φ (fun i => e (ρ i)).
induction φ; simpl; intros; try reflexivity.
*rewrite IHφ1, IHφ2; reflexivity.
*apply fa_morph; intros x.
 apply impl_morph; [reflexivity|intros].
 rewrite IHφ.
 apply Sat_resp_iff; [reflexivity|].
 destruct i; simpl; apply Equiv_refl.
Qed.

(*- Satisfaction depends only on the free variables. *)
Lemma sat_bound {M : PSet -> Prop} :
    forall {φ : Fml} {k : nat} {e e' : nat -> PSet}, Bound k φ -> (forall i, i < k -> e i ≈ e' i) ->
    (Sat M φ e <-> Sat M φ e').
induction φ; simpl; intros; try reflexivity.
*destruct H.
 eapply transitivity; [eapply mem_congr_left|eapply mem_congr_right]; auto.
*destruct H.
 split; intros.
 +eapply Equiv_trans; [apply Equiv_symm; apply H0|]; trivial.
  eapply Equiv_trans; [|apply H0]; trivial.
 +eapply Equiv_trans; [apply H0|]; trivial.
  eapply Equiv_trans; [|apply Equiv_symm; apply H0]; trivial.
*destruct H.
 apply impl_morph; [eapply IHφ1; eauto|symmetry;eapply IHφ2; eauto].
 intros; apply Equiv_symm; auto.
*apply fa_morph; intros x.
 apply fa_morph; intros.
 apply IHφ with (1:=H).
 destruct i; intros; [apply Equiv_refl|apply H0; auto with arith]. 
Qed.

(*! ### Derived connectives *)

Lemma sat_neg {M : PSet -> Prop} {φ : Fml} {e} : Sat M (neg φ) e <-> ~ Sat M φ e.
  reflexivity.
Qed.

Section em.
Hypothesis (em : forall p : Prop, p \/ ~p).

Lemma dne {p : Prop} (h : ~~p) : p.
destruct (em p); [trivial|].
destruct h; trivial.
Qed.
Lemma dne_iff {p : Prop} :  ~~p <-> p.
split; [apply dne|intro; auto].
Qed.

Lemma sat_and {M : PSet -> Prop} {φ ψ : Fml} {e} :
    Sat M (and φ ψ) e <-> Sat M φ e /\ Sat M ψ e.
simpl; split; [intros|destruct 1;auto].
edestruct em; [eassumption|].
destruct H; auto.
Qed.

Lemma sat_or {M : PSet -> Prop} {φ ψ : Fml} {e} :
    Sat M (or φ ψ) e <-> Sat M φ e \/ Sat M ψ e.
simpl; split; intros.
*edestruct em; [left;eassumption|]; auto.
*destruct H; [contradiction|trivial].
Qed.

Lemma sat_iff {M : PSet -> Prop} {φ ψ : Fml} {e} :
    Sat M (iff φ ψ) e <-> (Sat M φ e <-> Sat M ψ e).
unfold iff; rewrite sat_and.
reflexivity.
Qed.

Lemma sat_ex {M : PSet -> Prop} {φ : Fml} {e} :
    Sat M (ex φ) e <-> exists x, M x /\ Sat M φ (Env_cons x e).
simpl; split; intros.
*edestruct em; [eassumption|].
 destruct H; eauto.
*destruct H as (x,(?,?)); eauto.
Qed.

End em.

(*! ### Codes *)

Lemma ofNat_inj : forall {m n : nat}, ofNat m ≈ ofNat n -> m = n.
induction m; destruct n; intros.
*trivial.
*destruct (not_mem_empty (ofNat n)).
 apply (mem_congr_right H).
 apply mem_succ; right; apply Equiv_refl.
*destruct (not_mem_empty (ofNat m)).
 apply (mem_congr_right H).
 apply mem_succ; right; apply Equiv_refl.
*f_equal; apply IHm.
 apply succ_inj; trivial.
Qed.

(*- Codes: a tag followed by the components. *)
Fixpoint enc (f : Fml) : PSet :=
  match f with
  | mem i j => pair (ofNat 0) (pair (ofNat i) (ofNat j))
  | eq i j => pair (ofNat 1) (pair (ofNat i) (ofNat j))
  | fls => pair (ofNat 2) empty
  | imp φ ψ => pair (ofNat 3) (pair (enc φ) (enc ψ))
  | all φ => pair (ofNat 4) (enc φ)
  end.

Opaque Equiv ofNat.
Lemma enc_inj : forall {φ ψ : Fml}, enc φ ≈ enc ψ -> φ = ψ.
induction φ; destruct ψ; simpl; intros e;
  apply pair_inj in e; destruct e as (etag,e);
  apply ofNat_inj in etag; try discriminate.
*apply pair_inj in e; destruct e as (e1,e2).
 apply ofNat_inj in e1; apply ofNat_inj in e2; subst i0 j0; trivial.
*apply pair_inj in e; destruct e as (e1,e2).
 apply ofNat_inj in e1; apply ofNat_inj in e2; subst i0 j0; trivial.
*trivial.
*apply pair_inj in e; destruct e as (e1,e2).
 apply IHφ1 in e1; apply IHφ2 in e2.
 subst; trivial.
*apply IHφ in e; subst; trivial.
Qed.
