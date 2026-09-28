Require Import Fml PSet Pair VLevel Proof.
(*!
`ZF` as a first-order theory: extensionality, foundation, pairing, union, power set, infinity,
and the schemas of separation and replacement. Free variables of an axiom are parameters. The
replacement schema is in its usual form "a functional relation on `a` has its values in some
`b`"; with separation this gives the image.

`ZFModel M` lists closure conditions on a class of sets which make every axiom valid in it.
*)


(*- `forallz (z ∈ x <-> z ∈ y) -> x = y` *)
Definition Ax_ext : Fml := imp (all (iff (mem 0 1) (mem 0 2))) (eq 0 1).

(*- `existsz z ∈ x -> existsy (y ∈ x /\ forallz (z ∈ y -> z ∉ x))` *)
Definition Ax_found : Fml :=
  imp (ex (mem 0 1)) (ex (and (mem 0 1) (all (imp (mem 0 1) (neg (mem 0 2)))))).

(*- `existsz (x ∈ z /\ y ∈ z)` *)
Definition Ax_pair : Fml := ex (and (mem 1 0) (mem 2 0)).

(*- `existsu forally forallz (z ∈ y -> y ∈ x -> z ∈ u)` *)
Definition Ax_union : Fml := ex (all (all (imp (mem 0 1) (imp (mem 1 3) (mem 0 2))))).

(*- `existsp forally (forallz (z ∈ y -> z ∈ x) -> y ∈ p)` *)
Definition Ax_power : Fml := ex (all (imp (all (imp (mem 0 1) (mem 0 3))) (mem 0 1))).

(*- `existsw (existse (e ∈ w /\ forallz z ∉ e) /\ forally (y ∈ w -> existss (s ∈ w /\ forallz (z ∈ s <-> z ∈ y \/ z = y))))` *)
Definition Ax_inf : Fml :=
  ex (and (ex (and (mem 0 1) (all (neg (mem 0 1)))))
    (all (imp (mem 0 1) (ex (and (mem 0 2) (all (iff (mem 0 1) (or (mem 0 2) (eq 0 2))))))))).

Definition sepR (k:nat) : nat :=
  match k with
  | 0 => 0
  | S n => S(S n)
  end.

(*- `existsy forallz (z ∈ y <-> z ∈ x /\ ψ(z, params))`, where `ψ` has `z` as variable `0` and the free
variables of the axiom (`x` among them) as its variables `n+1`. *)
Definition Ax_sep (ψ : Fml) : Fml := ex (all (iff (mem 0 1) (and (mem 0 2) (rename sepR ψ)))).

Definition r1 (k:nat) : nat :=
  match k with
  | 0 => 2
  | 1 => 1
  | S (S n) => S(S(S n))
  end.

Definition r2 (k:nat) : nat :=
  match k with
  | 0 => 2
  | 1 => 0
  | S(S n) => S(S(S n))
  end.

Definition r3 (k:nat) : nat :=
  match k with
  | 0 => 0
  | 1 => 1
  | S(S n) => S(S(S n))
  end.

(*- `forallx (x ∈ a -> forally forally' (ψ(x,y) -> ψ(x,y') -> y = y')) -> existsb forally (existsx (x ∈ a /\ ψ(x,y)) -> y ∈ b)`,
where `ψ` has `x`, `y` as variables `0`, `1` and the free variables of the axiom (`a` among
them) as its variables `n+2`. *)
Definition Ax_repl (ψ : Fml) : Fml :=
  imp (all (imp (mem 0 1) (all (all (imp (rename r1 ψ) (imp (rename r2 ψ) (eq 1 0)))))))
    (ex (all (imp (ex (and (mem 0 3) (rename r3 ψ))) (mem 0 1)))).

(*- The axioms of `ZF`. *)
Inductive ZF : Fml -> Prop :=
  | V_ext : ZF Ax_ext
  | V_found : ZF Ax_found
  | V_pair : ZF Ax_pair
  | V_union : ZF Ax_union
  | V_power : ZF Ax_power
  | V_inf : ZF Ax_inf
  | V_sep (ψ : Fml) : ZF (Ax_sep ψ)
  | V_repl (ψ : Fml) : ZF (Ax_repl ψ).

(*- Closure conditions on a class which make it a model of `ZF`. *)
Class ZFModel (M : PSet -> Prop) : Prop := {
  M_trans : forall {x z}, M x -> z ∈ x -> M z;
  M_empty : M empty;
  M_upair : forall {x y}, M x -> M y -> M (upair x y);
  M_sUnion : forall {x}, M x -> M (sUnion x);
  M_powerset : forall {x}, M x -> M (powerset x);
  M_omega : M omega;
  M_sep : forall (P : PSet -> Prop) {x}, M x -> M (sep P x);
  M_repl : forall (ψ : Fml) (e : nat -> PSet), (forall i, M (e i)) -> forall a, M a ->
    (forall x y y', x ∈ a -> M y -> M y' -> Sat M ψ (Env_cons x (Env_cons y e)) ->
      Sat M ψ (Env_cons x (Env_cons y' e)) -> y ≈ y') ->
    #exists b, M b /\ forall x y, x ∈ a -> M y -> Sat M ψ (Env_cons x (Env_cons y e)) -> y ∈ b
  }.

(*- Every nonempty subset of a set has an `∈`-minimal element. *)
Lemma exists_minimal (em : forall p : Prop, #(p \/ ~p)) (x : PSet) :
  forall z, z ∈ x -> #exists y, y ∈ x /\ forall w, w ∈ y -> ~ w ∈ x.
intros z; elim z using @mem_induction; [prove_isL|clear z; intros z ih].
intros hz.
Tdestruct (em (exists w, w ∈ z /\ w ∈ x))
  as [(w& hw& hwx) | h]; [eauto|].
Texists z; split; trivial.
intros w hw hwx; apply h; eauto.
Qed.

Section ZFModel.
Context {M : PSet -> Prop} (hM : ZFModel M) (em : forall p : Prop, #(p \/ ~p)).

Lemma valid : forall φ, ZF φ -> Valid M φ.
intros φ h e he.
destruct h; simpl.
*intros h; apply ext; intros z.
 specialize h with z.
 rewrite (sat_iff em) in h; simpl in h.
 assert (aux: forall i, z ∈ e i -> M z).
 {intros i hz; apply M_trans with (1:=he i); trivial. }
 split; intros hz; generalize hz; apply h; eauto.
*intros h.
 rewrite (sat_ex em) in h.
 Tdestruct h as (z & ?& hz).
 Tdestruct (exists_minimal em (e 0) z hz) as (y& hy& hmin).
 apply (sat_ex em); Texists y; split;
   [apply M_trans with (1:=he 0); trivial|].
 rewrite (sat_and em); split; [trivial|].
 simpl; intros w ? hw hwx; eapply hmin; eauto.
*unfold Ax_pair; rewrite (sat_ex em).
 Texists (upair (e 0) (e 1)); split;
   [apply M_upair; trivial|].
 rewrite (sat_and em); simpl.
 split; apply mem_upair; [Tleft|Tright]; apply Equiv_refl.
*unfold Ax_union; rewrite (sat_ex em).
 Texists (sUnion (e 0)); split;
   [apply M_sUnion; trivial|].
 simpl; intros y ? z ? hz hy.
 apply mem_sUnion; Texists y; auto.
*unfold Ax_power; rewrite (sat_ex em).
 Texists (powerset (e 0)); split;
   [apply M_powerset; trivial|].
 simpl; intros y hy h.
 apply mem_powerset; intros; apply h; trivial.
 apply M_trans with (1:=hy); trivial.
*unfold Ax_inf; rewrite (sat_ex em).
 Texists omega; split;
   [apply M_omega; trivial|].
 rewrite (sat_and em), (sat_ex em); simpl.
 split.
 **Texists empty; split; [apply M_empty|].
   rewrite (sat_and em); simpl.
   split; [apply mem_omega; Texists 0; apply Equiv_refl|].
   intros z ? hz.
   apply not_mem_empty in hz; contradiction.
 **intros x ? hx.
   rewrite mem_omega in hx; Tdestruct hx as (n,e').
   assert (e'' := succ_congr e').
   rewrite (sat_ex em).
   Texists (succ x).   
   split.
   {apply M_trans with (1:=M_omega).
    rewrite mem_omega; Texists (S n); trivial. }
   {rewrite (sat_and em); simpl.
    split; [rewrite mem_omega; Texists (S n); trivial|].
    intros z ?.
    rewrite (sat_iff em), (sat_or em); simpl.
    apply mem_succ. }
*unfold Ax_sep; rewrite (sat_ex em); simpl.
 pose (P (*: PSet -> Prop*) := fun z => Sat M ψ (Env_cons z e)).
 assert (Pok : forall x, isL(P x)) by (unfold P; prove_isL).
 assert (hP : forall z z', z ≈ z' -> P z -> P z').
 {intros ?? ez; apply Sat_resp; apply Env_cons_resp;
     [trivial|intros; apply Equiv_refl]. }
 Texists (sep P (e 0)); split;
   [apply M_sep; trivial|].
 intros z ?.
 rewrite (sat_iff em), (sat_and em); simpl.
 rewrite mem_sep; [|prove_isL|trivial].
 apply and_iff_morphism; [reflexivity|].
 rewrite sat_rename.
 unfold P.
 apply Sat_resp_iff; [reflexivity|].
 unfold sepR.
 destruct i as [|i]; simpl; apply Equiv_refl.
*intros hf.
 assert (R2 : forall {x y y'},
            Sat M ψ (Env_cons x (Env_cons y' e)) ->
            Sat M (rename r2 ψ) (Env_cons y' (Env_cons y (Env_cons x e)))).
 {intros ???.
  rewrite sat_rename.  
  apply Sat_resp.
  unfold r2.
  destruct i as [|[|i]]; apply Equiv_refl. }
 assert (R1' : forall {x y y'},
            Sat M ψ (Env_cons x (Env_cons y e)) ->
            Sat M (rename r1 ψ) (Env_cons y' (Env_cons y (Env_cons x e)))).
 {intros ???.
  rewrite sat_rename.  
  apply Sat_resp.
  unfold r1.
  destruct i as [|[|i]]; apply Equiv_refl. }
 Tdestruct (M_repl ψ e he (e 0)) as (b& hb& hb'); auto.
 {rewrite (sat_ex em); simpl.
  Texists b; split; trivial.
  intros y hy h.
  rewrite (sat_ex em) in h.
  Tdestruct h as (x& ?& hx).
  rewrite (sat_and em) in hx; simpl in hx.
  destruct hx as (hxa, hs).
  apply hb' with x; trivial.
  rewrite sat_rename in hs.
  revert hs; apply Sat_resp.
  unfold r3.
  destruct i as [|[|i]]; apply Equiv_refl. }
 {intros x y y' hx hy hy' h1 h2.
  apply R1' with (y':=y') in h1.
  apply R2 with (y:=y) in h2.
  revert h1 h2; apply hf; auto.
  apply M_trans with (1:=he 0); trivial. }
Qed.

Lemma con : Con ZF.
apply (@Con_of_model em) with (M:=M) (x:=empty);
  [exact valid|apply M_empty].
Qed.

End ZFModel.
