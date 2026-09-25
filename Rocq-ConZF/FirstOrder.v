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
Admitted.
(*| 0, _, _, _, _, h => (Nat.not_lt_zero _ h).elim
  | _+1, _, _, h, 0, _ => (pair_inj h).1
  | _+1, _, _, h, i+1, hi => tup_inj (pair_inj h).2 i (Nat.lt_of_succ_lt_succ hi)*)

Definition ISat (η q x y : PSet) : Prop :=
  exists φ k e, q ≈ pair (enc φ) (pair (ofNat k) (tup k e)) /\ Bound (S(S k)) φ /\
    x ∈ Vl η /\ y ∈ Vl η /\ Sat (fun x=>x ∈ Vl η) φ (Env_cons x (Env_cons y e)).

Section em.
Hypothesis (em : forall p : Prop, p \/ ~p).

Lemma Vl_congr {η η' : PSet} (e : η ≈ η') : Vl η ≈ Vl η'.
Admitted.
(*ext fun _ => (mem_Vl em).trans <| (mem_congr_right (rank_congr e)).trans (mem_Vl em).symm*)

Lemma ISat_resp {η η' q q' x x' y y' : PSet} (eη : η ≈ η') (eq : q ≈ q') (ex : x ≈ x')
    (ey : y ≈ y') (h : ISat η q x y) : ISat η' q' x' y'.
Admitted.
(*have ⟨φ, k, e, hq, hb, hx, hy, hs⟩ := h
  have eV := Vl_congr em eη
  ⟨φ, k, e, eq.symm.trans hq, hb, (mem_congr_right eV).1 ((mem_congr_left ex).1 hx),
    (mem_congr_right eV).1 ((mem_congr_left ey).1 hy),
    (Sat.resp_iff (fun _ => mem_congr_right eV) φ
      (Env.cons_resp ex (Env.cons_resp ey fun _ => Equiv.refl _))).1 hs⟩*)

Lemma Vl_trans {ρ y z : PSet} (hy : y ∈ Vl ρ) (hz : z ∈ y) : z ∈ Vl ρ.
Admitted.
(*(mem_Vl em).2 ((isOrd_rank ρ).trans _ ((mem_Vl em).1 hy) _ (rank_mem hz))*)

Lemma limit_succ_mem {ρ ζ : PSet} (hρ : IsOrd ρ) (hs : ~ IsSucc ρ) (hζ : ζ ∈ ρ) :
    succ ζ ∈ ρ.
Admitted.
(*refine ((hρ.mem hζ).succ.subset em hρ fun z hz => ?_).resolve_right fun e => hs ⟨ζ, e.symm⟩
  rcases mem_succ.1 hz with hz | e
  · exact hρ.trans ζ hζ z hz
  · exact (mem_congr_left e).2 hζ*)

Lemma omega_mem {ρ : PSet} (hρ : IsOrd ρ) (h0 : ~ ρ ≈ empty) (hs : ~ IsSucc ρ)
    (hω : ~ ρ ≈ omega) : omega ∈ ρ.
Admitted.
(*rcases isOrd_omega.trichotomy em hρ with h | e | h
  · exact h
  · exact (hω e.symm).elim
  · have ⟨n, e⟩ := mem_omega.1 h
    cases n with
    | zero => exact (h0 e).elim
    | succ n => exact (hs ⟨ofNat n, e⟩).elim*)

(*- Two elements of an ordinal are included in a third. *)
Lemma exists_upper {ρ a b : PSet} (hρ : IsOrd ρ) (ha : a ∈ ρ) (hb : b ∈ ρ) :
    exists R, R ∈ ρ /\ (forall z, z ∈ a -> z ∈ R) /\ (forall z, z ∈ b -> z ∈ R).
Admitted.
(*rcases (hρ.mem ha).trichotomy em (hρ.mem hb) with h | e | h
  · exact ⟨b, hb, fun z hz => (hρ.mem hb).trans a h z hz, fun _ hz => hz⟩
  · exact ⟨b, hb, fun _ hz => (mem_congr_right e).1 hz, fun _ hz => hz⟩
  · exact ⟨a, ha, fun _ hz => hz, fun z hz => (hρ.mem ha).trans b h z hz⟩*)

End em.

Lemma ofNat_mono {x : PSet} : forall {m n : nat}, m <= n -> x ∈ ofNat m -> x ∈ ofNat n.
Admitted.
(*| _, 0, h, hx => by cases Nat.le_zero.1 h; exact hx
  | m, n+1, h, hx => by
    rcases Nat.lt_or_ge n m with h' | h'
    · cases Nat.le_antisymm h (Nat.succ_le_of_lt h'); exact hx
    · exact mem_succ.2 (.inl (ofNat_mono h' hx))*)

Lemma rank_ofNat_mem (n : nat) : rank (ofNat n) ∈ ofNat (n+1).
Admitted.
(*(mem_congr_left (isOrd_ofNat n).rank_equiv).2 (mem_succ.2 (.inr (Equiv.refl _)))*)

Lemma rank_pair_ofNat (em : forall p : Prop, p \/ ~p) {a b : PSet} {m n : nat}
    (ha : rank a ∈ ofNat m) (hb : rank b ∈ ofNat n) : rank (pair a b) ∈ ofNat (max m n + 2).
Admitted.
(*rank_pair_mem em (isOrd_ofNat _) (ofNat_mono (Fml.le_nmax_left m n) ha)
    (ofNat_mono (Fml.le_nmax_right m n) hb)*)

(** All formulae have a finite rank *)
Lemma rank_enc_mem (em : forall p : Prop, p \/ ~p) : forall φ : Fml, exists n, rank (enc φ) ∈ ofNat n.
Admitted.
(*| .mem i j | .eq i j => ⟨_, rank_pair_ofNat em (rank_ofNat_mem _)
      (rank_pair_ofNat em (rank_ofNat_mem i) (rank_ofNat_mem j))⟩
  | .fls => ⟨_, rank_pair_ofNat em (rank_ofNat_mem 2) (n := 1)
      ((mem_congr_left (isOrd_empty.rank_equiv)).2 (mem_succ.2 (.inr (Equiv.refl _))))⟩
  | .all φ => have ⟨_, h⟩ := rank_enc_mem em φ
      ⟨_, rank_pair_ofNat em (rank_ofNat_mem _) h⟩
  | .imp φ ψ => have ⟨_, h1⟩ := rank_enc_mem em φ; have ⟨_, h2⟩ := rank_enc_mem em ψ
      ⟨_, rank_pair_ofNat em (rank_ofNat_mem _) (rank_pair_ofNat em h1 h2)⟩*)

Lemma mem_succN {R x : PSet} (h : x ∈ R) : forall n, x ∈ succN n R.
Admitted.
(*| 0 => h
  | n+1 => mem_succ.2 (.inl (mem_succN h n))*)

Fixpoint tupN (n:nat) : nat :=
  match n with
  | 0 => 1
  | S k => S(S(tupN k))
  end.

Lemma rank_tup_mem (em : forall p : Prop, p \/ ~p) {R : PSet} (hR : IsOrd R) :
    forall {k : nat} {e : nat -> PSet}, (forall i, i < k -> rank (e i) ∈ R) ->
      rank (tup k e) ∈ succN (tupN k) R.
Admitted.
(*| 0, _, _ => rank_mem_succ em hR fun _ h => (not_mem_empty _ h).elim
  | k+1, _, h =>
    rank_pair_mem em (hR.iterate_succ (tupN k)) (mem_succN (h 0 (Nat.succ_pos k)) _)
      (rank_tup_mem em hR fun i hi => h (i+1) (Nat.succ_lt_succ hi))
*)
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
Admitted. (*  (mem_Vl em).2 ((mem_congr_right hρ.rank_equiv).2 hz)*)

(*omit h0 hω in*)
(*- A set all of whose elements have rank below some `R ∈ ρ` is in `V_ρ`. *)
Lemma mem_Vl_of_bound {y R : PSet} (hR : R ∈ ρ) (h : forall z, z ∈ y -> rank z ∈ R) :
    y ∈ Vl ρ.
Proof using em hρ hs.
Admitted. (*  mem_Vl_of_rank em hρ <| hρ.trans _ (limit_succ_mem em hρ hs hR) _
    (rank_mem_succ em (hρ.mem hR) h)*)

(*- Finitely many elements of `V_ρ` have ranks below some `R ∈ ρ`. *)
Lemma exists_bound_tup : forall (k : nat) (e : nat -> PSet), (forall i, i < k -> e i ∈ Vl ρ) ->
    exists R, R ∈ ρ /\ forall i, i < k -> rank (e i) ∈ R.
Admitted.
(*| 0, _, _ => ⟨omega, omega_mem em hρ h0 hs hω, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | k+1, e, he => by
    have ⟨R, hR, h⟩ := exists_bound_tup k e fun i hi => he i (Nat.lt_succ_of_lt hi)
    have ⟨R', hR', h1, h2⟩ := exists_upper em hρ hR
      (limit_succ_mem em hρ hs (rank_lt_of_mem em hρ (he k (Nat.lt_succ_self k))))
    refine ⟨R', hR', fun i hi => ?_⟩
    rcases Nat.lt_or_ge i k with hi' | hi'
    · exact h1 _ (h i hi')
    · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) hi'
      exact h2 _ (mem_succ.2 (.inr (Equiv.refl _)))*)

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
