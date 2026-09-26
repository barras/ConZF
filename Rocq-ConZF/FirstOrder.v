Require Import PSet Fml ZF VLevel Pair Ord Worldly.
(*!
The first-order instance of the dichotomy. `ISat η q x y`: `q` codes a formula `φ`, a number
`k` and a `k`-tuple of parameters, the free variables of `φ` are below `k+2`, and
`V_η ⊨ φ[x, y, params]`. An ordinal that is not `0`, not a successor, not `ω` and not reachable
for `ISat` is a limit above `ω`, and `V_ρ` is a model of `ZF`.
*)
  
(*- `k`-tuples, as nested pairs. *)
Fixpoint tup (n : nat) (e:nat -> PSet) : PSet :=
  match n with
  | 0 => empty
  | S k => pair (e 0) (tup k (fun i => e (S i)))
  end.

Lemma tup_inj : forall {k : nat} {e e' : nat -> PSet}, tup k e ≈ tup k e' -> forall i, i < k -> e i ≈ e' i.
induction k; [intros ?? _ i lt0; inversion lt0|].
intros e e' et.
simpl tup in et;apply pair_inj in et; destruct et as (e0, eS).
specialize IHk with (1:=eS); simpl in IHk.
intros [|i] ltk; auto with arith.
Qed.

Definition ISat (η q x y : PSet) : Prop :=
  exists φ k e, q ≈ pair (enc φ) (pair (ofNat k) (tup k e)) /\ Bound (S(S k)) φ /\
    x ∈ Vl η /\ y ∈ Vl η /\ Sat (fun x=>x ∈ Vl η) φ (Env_cons x (Env_cons y e)).

Section em.
Hypothesis (em : forall p : Prop, p \/ ~p).

Lemma Vl_congr {η η' : PSet} (e : η ≈ η') : Vl η ≈ Vl η'.
apply ext; intros z.
rewrite !(mem_Vl em).
apply mem_congr_right.
apply rank_congr; trivial.
Qed.

Lemma ISat_resp {η η' q q' x x' y y' : PSet} (eη : η ≈ η') (eq : q ≈ q') (ex : x ≈ x')
    (ey : y ≈ y') (h : ISat η q x y) : ISat η' q' x' y'.
destruct h as (φ& k& e& hq& hb& hx& hy& hs).
assert (eV := Vl_congr eη).
apply Equiv_symm in eV.
exists φ; exists k; exists e; split;[|split;[|split;[|split]]]; trivial.
*eauto using Equiv_trans, Equiv_symm.
*apply mem_congr_left with (1:=ex). 
 revert hx; apply mem_congr_right; trivial. 
*apply mem_congr_left with (1:=ey). 
 revert hy; apply mem_congr_right; trivial. 
*revert hs.
 apply Sat_resp_iff.
 +intro; apply mem_congr_right; trivial.
 +intro; apply Equiv_symm; apply Env_cons_resp;[|apply Env_cons_resp]; trivial.
  intros; apply Equiv_refl.
Qed.

Lemma Vl_trans {ρ y z : PSet} (hy : y ∈ Vl ρ) (hz : z ∈ y) : z ∈ Vl ρ.
apply (mem_Vl em).
apply (mem_Vl em) in hy.
assert (o := isOrd_rank ρ).
apply (IsOrd_trans _) with (1:=hy).
apply rank_mem; trivial.
Qed.

Lemma limit_succ_mem {ρ ζ : PSet} (hρ : IsOrd ρ) (hs : ~ IsSucc ρ) (hζ : ζ ∈ ρ) :
    succ ζ ∈ ρ.
destruct (@IsOrd_subset em (succ ζ) ρ); trivial.
*apply IsOrd_succ.
 apply IsOrd_mem with (2:=hζ); trivial.
*intros.
 apply mem_succ in H; destruct H.
 +apply (IsOrd_trans _) with (2:=H); trivial.
 +revert hζ; apply mem_congr_left; trivial.
*elim hs.
 exists ζ; apply Equiv_symm; trivial.
Qed.

Lemma omega_mem {ρ : PSet} (hρ : IsOrd ρ) (h0 : ~ ρ ≈ empty) (hs : ~ IsSucc ρ)
    (hω : ~ ρ ≈ omega) : omega ∈ ρ.
destruct (@IsOrd_trichotomy em) with (1:=isOrd_omega)(2:=hρ) as [h |[e | h]].
*trivial.
*apply Equiv_symm in e; contradiction.
*apply mem_omega in h.
 destruct h as ([|n],e).
 +contradiction.
 +elim hs; exists (ofNat n); trivial.
Qed.

(*- Two elements of an ordinal are included in a third. *)
Lemma exists_upper {ρ a b : PSet} (hρ : IsOrd ρ) (ha : a ∈ ρ) (hb : b ∈ ρ) :
    exists R, R ∈ ρ /\ (forall z, z ∈ a -> z ∈ R) /\ (forall z, z ∈ b -> z ∈ R).
(*  exists (iUnion (fun i:bool => if i then a else b)).*)
destruct (@IsOrd_trichotomy em)
  with (1:=IsOrd_mem _ ha) (2:=IsOrd_mem _ hb) as [h |[e | h]].
*exists b; split; [|split]; auto.
 intros.
 apply IsOrd_mem with (2:=hb) in hρ.
 apply (IsOrd_trans _) with (2:=H); trivial.
*exists b; split; [|split]; auto.
 intros z; apply mem_congr_right with (1:=e).
*exists a; split; [|split]; auto.
 intros.
 apply IsOrd_mem with (2:=ha) in hρ.
 apply (IsOrd_trans _) with (2:=H); trivial.
Qed.

End em.

Lemma ofNat_mono {x : PSet} : forall {m n : nat}, m <= n -> x ∈ ofNat m -> x ∈ ofNat n.
induction 1; [trivial|intro h].
apply IHle in h.
simpl ofNat; apply mem_succ; left; trivial.
Qed.

Lemma rank_ofNat_mem (n : nat) : rank (ofNat n) ∈ ofNat (S n).
eapply mem_congr_left; [eapply IsOrd_rank_equiv; apply isOrd_ofNat|].
simpl ofNat; apply mem_succ; right; apply Equiv_refl.
Qed.

Lemma rank_pair_ofNat (em : forall p : Prop, p \/ ~p) {a b : PSet} {m n : nat}
    (ha : rank a ∈ ofNat m) (hb : rank b ∈ ofNat n) : rank (pair a b) ∈ ofNat (S (S (max m n))).
simpl ofNat.
eapply (rank_pair_mem em).
*apply isOrd_ofNat.  
*apply ofNat_mono with (2:=ha); auto with arith.
*apply ofNat_mono with (2:=hb); auto with arith.
Qed.

(** All formulae have a finite rank *)
Lemma rank_enc_mem (em : forall p : Prop, p \/ ~p) : forall φ : Fml, exists n, rank (enc φ) ∈ ofNat n.
induction φ.
*eexists.
 eapply (rank_pair_ofNat em (rank_ofNat_mem _)).
 eapply (rank_pair_ofNat em (rank_ofNat_mem _)).
 eapply (rank_ofNat_mem j).
*eexists.
 eapply (rank_pair_ofNat em (rank_ofNat_mem _)).
 eapply (rank_pair_ofNat em (rank_ofNat_mem _)).
 eapply (rank_ofNat_mem j).
*eexists.
 eapply (rank_pair_ofNat em (rank_ofNat_mem _)).
 eapply (rank_ofNat_mem 0).
*destruct IHφ1 as (n1,h1).
 destruct IHφ2 as (n2,h2).
 unfold enc; fold enc.
 eexists.
 eapply (rank_pair_ofNat em (rank_ofNat_mem _)).
 eapply (rank_pair_ofNat em h1 h2).
*destruct IHφ as (n,h).
 unfold enc; fold enc.
 eexists.
 eapply (rank_pair_ofNat em (rank_ofNat_mem _) h).
Qed.

Lemma mem_succN {R x : PSet} (h : x ∈ R) : forall n, x ∈ succN n R.
induction n; simpl succN; [trivial|].
apply mem_succ; auto.
Qed.

Fixpoint tupN (n:nat) : nat :=
  match n with
  | 0 => 1
  | S k => S(S(tupN k))
  end.

Lemma rank_tup_mem (em : forall p : Prop, p \/ ~p) {R : PSet} (hR : IsOrd R) :
    forall {k : nat} {e : nat -> PSet}, (forall i, i < k -> rank (e i) ∈ R) ->
      rank (tup k e) ∈ succN (tupN k) R.
induction k; simpl succN; simpl tupN; simpl tup.
*intros e _.
 apply (rank_mem_succ em hR); intros.
 apply not_mem_empty in H; contradiction.
*intros e he. 
 apply (rank_pair_mem em (IsOrd_iterate_succ hR _)).
 +apply mem_succN; auto with arith.
 +apply IHk.
  intros; apply he; auto with arith.
Qed.

(*! ### The second horn *)

Section SecondHorn.
Context (em : forall p : Prop, p \/ ~p) {ρ : PSet} (hρ : IsOrd ρ) (h0 : ~ ρ ≈ empty)
  (hs : ~ IsSucc ρ) (hω : ~ ρ ≈ omega).


(*omit h0 hs hω in*)
Lemma rank_lt_of_mem {z : PSet} (hz : z ∈ Vl ρ) : rank z ∈ ρ.
Proof using em hρ.
apply mem_congr_right with (1:= IsOrd_rank_equiv hρ).
apply mem_Vl with (1:=em); trivial.
Qed.

(*omit h0 hs hω in*)
Lemma mem_Vl_of_rank {z : PSet} (hz : rank z ∈ ρ) : z ∈ Vl ρ.
Proof using em hρ.
apply (mem_Vl em).
revert hz; apply mem_congr_right.
apply IsOrd_rank_equiv; trivial.
Qed.

(*omit h0 hω in*)
(*- A set all of whose elements have rank below some `R ∈ ρ` is in `V_ρ`. *)
Lemma mem_Vl_of_bound {y R : PSet} (hR : R ∈ ρ) (h : forall z, z ∈ y -> rank z ∈ R) :
    y ∈ Vl ρ.
Proof using em hρ hs.
apply mem_Vl_of_rank.
assert (hRs := hR).  
apply (limit_succ_mem em) in hRs; trivial.
apply (IsOrd_trans _) with (1:=hRs).
apply (rank_mem_succ em); trivial.
apply IsOrd_mem with (2:=hR); trivial.
Qed.

(*- Finitely many elements of `V_ρ` have ranks below some `R ∈ ρ`. *)
Lemma exists_bound_tup : forall (k : nat) (e : nat -> PSet), (forall i, i < k -> e i ∈ Vl ρ) ->
    exists R, R ∈ ρ /\ forall i, i < k -> rank (e i) ∈ R.
induction k.
*exists omega; split.
 +apply (omega_mem em); auto.
 +intros i lt0; inversion lt0.
*intros e he.
 destruct IHk with (e:=fun i=>e(S i)) as (R& hR& h).
 {intros; apply he; auto with arith. }
 assert (he0 : e 0 ∈ Vl ρ) by auto with arith.
 apply rank_lt_of_mem in he0.
 apply (limit_succ_mem em) in he0; trivial.
 destruct (@exists_upper em) with (2:=hR) (3:=he0) as (R'& hR'& h1& h2); trivial.
 exists R'; split; trivial.
 intros [|i] ltk.
 +apply h2; apply mem_succ; right; apply Equiv_refl.
 +apply h1; auto with arith.
Qed.  

Lemma Vl_model (hr : forall ν, ν ∈ ρ -> ~ Reach ISat ρ ν) : ZFModel (fun z => z ∈ Vl ρ).
assert (hωρ := omega_mem em hρ h0 hs hω).
assert (Vρ : forall {y R : PSet}, R ∈ ρ -> (forall z, z ∈ y -> rank z ∈ R) -> y ∈ Vl ρ).
{intros ?? hR h.
 apply mem_Vl_of_bound (*em hρ hs*) with (1:=hR) (2:=h). }
assert (rρ : forall {z}, z ∈ Vl ρ -> rank z ∈ ρ).
{intros z; apply rank_lt_of_mem. }
split.
*apply Vl_trans; exact em.
*apply Vρ with (1:=hωρ).
 intros ? h.
 apply not_mem_empty in h; contradiction.
*intros ?? hx hy.
 destruct exists_upper with (1:=em) (2:=hρ)
                            (3:=limit_succ_mem em hρ hs (rρ _ hx))
                            (4:=limit_succ_mem em hρ hs (rρ _ hy))
   as (R & hR & h1 & h2).
 apply Vρ with (1:=hR).
 intros z hz; apply mem_upair in hz; destruct hz as [e|e]; [apply h1|apply h2].
 +eapply mem_congr_left; [|apply mem_succ;right;apply Equiv_refl].
  apply rank_congr; trivial.
 +eapply mem_congr_left; [|apply mem_succ;right;apply Equiv_refl].
  apply rank_congr; trivial.
*intros ? hx.
 apply Vρ with (1:=rρ _ hx).
 intros z hz; apply mem_sUnion in hz.
 destruct hz as (w & hw & hzw).
 eapply (@IsOrd_trans _ (isOrd_rank x));
   [apply rank_mem with (1:=hw)|apply rank_mem with (1:=hzw)].
*intros ? hx.
 apply Vρ with (1:=limit_succ_mem em hρ hs (rρ _ hx)).
 intros z hz.
 apply rank_mem_succ with (1:=em) (2:=isOrd_rank _).
 intros w hw; apply rank_mem.
 rewrite mem_powerset in hz; auto.
*apply mem_Vl_of_rank.
 apply mem_congr_left with (2:=hωρ).
 apply IsOrd_rank_equiv.
 apply isOrd_omega.
*intros ?? hx.
 apply Vρ with (1:=rρ _ hx).
 intros ? ((i,?),e).
 simpl in e.
 apply rank_mem.
 exists i; trivial.
* (* Replacement *)
  intros ψ e he a ha hf.
  destruct (exists_bound ψ) as (m, hm).
  assert (hb : Bound (S (S m)) ψ).
  {apply Bound_mono with (2:=hm); auto with arith. }
  pose (q := pair (enc ψ) (pair (ofNat m) (tup m e))).
  (*-- a bound `ν ∈ ρ` for the ranks of `q` and `a` *)
  destruct exists_bound_tup with m e as (R0 & hR0 & hR0e); auto.
  destruct exists_upper with (1:=em) (2:=hρ) (3:=hR0) (4:=hωρ)
    as (R1 & hR1 & hR0R1& hωR1).
  destruct  exists_upper with (1:=em) (2:=hρ) (3:=hR1)
                              (4:=limit_succ_mem em hρ hs (rρ _ ha))
    as (R & hR & hR1R & haR).
  assert (hRo (*: IsOrd R*) := IsOrd_mem hρ hR).
  pose (T := succN (tupN m) R).
  assert (hTo : IsOrd T) by (apply IsOrd_iterate_succ; trivial).
  assert (hT : T ∈ ρ).
  {unfold T; generalize (tupN m).
   induction n; [trivial|].
   apply limit_succ_mem with (1:=em); trivial. }
  assert (hRT : forall {z}, z ∈ R -> z ∈ T).
  {intros ? h; apply  mem_succN; trivial. }
  destruct (rank_enc_mem em ψ) as (n, hn).
  assert (hω' : forall {z}, z ∈ omega -> z ∈ T) by auto.
  assert (hq : rank q ∈ succN 4 T).
  {apply rank_pair_mem with (1:=em); auto using IsOrd_succ.
   *apply mem_succ; left; apply mem_succ; left.
    apply hω'.
    eapply(@IsOrd_trans _ isOrd_omega) with (2:=hn).
    exists n; apply Equiv_refl. 
   *apply rank_pair_mem with (1:=em); auto using IsOrd_succ.
    **apply hω'.
      eapply mem_congr_left; [|exists m; apply Equiv_refl].
      apply IsOrd_rank_equiv.
      apply isOrd_ofNat.
    **apply rank_tup_mem with (1:=em); auto. }
  pose (ν := succN 5 T).
  assert (hν : ν ∈ ρ).
  {unfold ν; generalize 5 as k.
   induction k; [trivial|].
   apply limit_succ_mem with (1:=em); trivial. }
  assert (haν : rank a ∈ ν).
  {apply mem_succN.
   apply hRT.
   apply haR.
   apply mem_succ; right; apply Equiv_refl. }
  assert (hqν : rank q ∈ ν) by (apply mem_succ; auto).
  (*-- the relation, and its instances of `ISat`*)
  pose (Rl := fun x y => Sat (fun x=>x ∈ Vl ρ) ψ (Env_cons x (Env_cons y e))).
  assert (hI : forall {x y}, x ∈ a -> y ∈ Vl ρ -> Rl x y -> ISat ρ q x y).
  {intros ?? hx hy h.
   exists ψ; exists m; exists e;
     split; [apply Equiv_refl|split;[|split;[|split]]]; trivial.
   eauto using Vl_trans. }
  assert (hI' : forall {x y}, ISat ρ q x y -> y ∈ Vl ρ /\ Rl x y).
  {intros x y (φ & k & e' & eq & hb' & _ & hy & h).
   apply pair_inj in eq; destruct eq as (e1,e2).
   apply enc_inj in e1; subst φ.
   apply pair_inj in e2; destruct e2 as (e3,e4).
   apply ofNat_inj in e3; subst k.   
   split; [trivial|].
   apply sat_bound with (1:=hb)(3:=h).
   destruct i as [|[|i]]; intros; try apply Equiv_refl.
   simpl.
   apply tup_inj with (1:=e4); eauto with arith. }
  assert (notunb : ~ forall ζ, ζ ∈ ρ -> exists x y, x ∈ a /\ ISat ρ q x y /\ ζ ∈ succ (rank y)).
  {intros h.
   apply hr with (1:=hν).
   (* Reach... *)   
   exists q; exists a.
   split; [|split]; trivial.
   split; [|split].
   *intros x y y' hx h1 h2.
    destruct (hI' _ _ h1) as (hy, s1); destruct (hI' _ _ h2) as (hy', s2).
    eauto.
   *intros ??? h1; apply rρ; apply (hI' _ _ h1).
   *exact h. }
  assert (hbd : exists ζ, ζ ∈ ρ /\ ~ exists x y, x ∈ a /\ ISat ρ q x y /\ ζ ∈ succ (rank y)).
  {edestruct em as [?|h]; [eassumption|].
   destruct notunb; intros ζ hζ.
   edestruct em as [|h']; [eassumption|].
   destruct h; eauto. }
  destruct hbd as (ζ & hζ & hbd).
  assert (hζo : IsOrd ζ). apply IsOrd_mem with (2:=hζ); trivial.
  assert (bound : forall {x y}, x ∈ a -> y ∈ Vl ρ -> Rl x y -> rank y ∈ ζ).
  {intros x y hx hy h.
   destruct IsOrd_trichotomy with (1:=em) (2:=isOrd_rank y) (3:=hζo)
     as [h'|[e'|h']]; trivial.
   *destruct hbd.
    exists x; exists y.
    split; [|split]; auto.
    apply mem_succ; right; apply Equiv_symm; trivial.
   *destruct hbd.
    exists x; exists y.
    split; [|split]; auto.
    apply mem_succ; left; trivial. }
  exists (Vl ζ); split.
  +apply Vρ with (1:=hζ).
   intros z hz; eapply mem_congr_right with (1:=IsOrd_rank_equiv hζo).
   apply (mem_Vl em); trivial.
  +intros x y hx hy h.
   apply (mem_Vl em).
   eapply mem_congr_right with (1:=IsOrd_rank_equiv hζo).
   eapply bound with (1:=hx); trivial.
Qed.

End SecondHorn.

(*! ### The first horn *)

Lemma V_model (hrepl : forall (s : PSet) (φ : PSet -> PSet -> Prop),
      (forall {x x' y y'}, x ≈ x' -> y ≈ y' -> φ x y -> φ x' y') ->
      (forall {x y y'}, x ∈ s -> φ x y -> φ x y' -> y ≈ y') ->
      exists img : PSet, forall y, y ∈ img <-> exists x, x ∈ s /\ φ x y) :
  ZFModel (fun _ : PSet => True).
split; trivial.
intros ψ e  _ a _ hf.
destruct(hrepl a (fun x y => Sat (fun _ => True) ψ (Env_cons x (Env_cons y e))))
  as (b, hb); [|eauto|].
{intros ???? eqx eqy.
 apply Sat_resp.
 destruct i as [|[|i]]; simpl; trivial.
 apply Equiv_refl. }
exists b; split; [trivial|].
intros.
apply hb.
exists x; auto.
Qed.

(*- **Lean without choice, with excluded middle, proves the consistency of `ZF`.** The model
is the sets-as-trees if they satisfy Replacement, and otherwise `V_ρ` for an ordinal `ρ` that
is not reachable by the definability rule. *)
Lemma con_ZF (em : forall p : Prop, p \/ ~p) : Con ZF.
destruct dichotomy with (I:=ISat) (1:=@ISat_resp em) (2:=em)
  as [h | (p & hρ & h0 & hs & hω & hr)].
*apply con with (2:=em) (1:=V_model h).
*apply con with (2:=em) (1:=Vl_model em hρ h0 hs hω hr).
Qed.

(*- info: 'PSet.con_ZF' does not depend on any axioms *)
Print Assumptions con_ZF.
