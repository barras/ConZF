Require Import Rule VLevel.
(*!
The definability rule (doc/main.tex, section 5).

`I η q x y` is an arbitrary notion of "`y` is the value at `x` of the function defined over
`V_η` with parameter `q`". For the theorem in the paper it is satisfaction of a formula over
`V_η`, with `q` a pair of a formula code and a parameter; nothing here depends on that.
A limit `η > ω` is *reachable* if some `I`-definable function with parameters of rank below some
`ν ∈ η` has values of rank unbounded in `η`. The rule gives every ordinal that is `0`, a successor,
`ω` or reachable a coherent assignment. So either every ordinal has one, and then Replacement
holds, or some ordinal is none of these, which is a limit above `ω` into which no definable
function from a smaller set is cofinal (for first-order `I`: a worldly cardinal).
*)

Import PSet Ord Pair Mat.

Section S.
Context (I : PSet -> PSet -> PSet -> PSet -> Prop).

(*- `(q, s)` defines, over `V_η`, a partial function on `s` with values of rank unbounded in `η`. *)
Definition Unb (η q s : PSet) : Prop :=
  (forall x y y', x ∈ s -> I η q x y -> I η q x y' -> y ≈ y') /\
  (forall x y, x ∈ s -> I η q x y -> rank y ∈ η) /\
  (forall ζ, ζ ∈ η -> exists x y, x ∈ s /\ I η q x y /\ ζ ∈ succ (rank y)).

(*- `η` is reached from parameters of rank below `ν`. *)
Definition Reach (η ν : PSet) : Prop := exists q s, rank q ∈ ν /\ rank s ∈ ν /\ Unb η q s.

Definition IsSucc (η : PSet) : Prop := exists ζ, η ≈ succ ζ.

(*- The case of the rule that uses definable functions. *)
Definition LimCase (η : PSet) : Prop := ~ IsSucc η /\ ~ η ≈ omega /\ exists ν, ν ∈ η /\ Reach η ν.

(*- The least `ν` from which `η` is reached, as the set of the `ν ∈ η` from which it is not. *)
Definition Gν (η : PSet) : PSet := sep (fun ν => ~ Reach η ν) η.

(*- The target of the child `a`. *)
Definition RuleA (η ξ : PSet) : Prop :=
  η ≈ succ ξ \/ (η ≈ omega /\ ξ ≈ empty) \/ (LimCase η /\ ξ ≈ Gν η).

(*- The target of the child `b w`. *)
Definition RuleB (η w ξ : PSet) : Prop :=
  (η ≈ omega /\ rank w ∈ omega /\ ξ ≈ rank w) \/
  (LimCase η /\ exists q s x y, w ≈ triple q s x /\ Unb η q s /\ x ∈ s /\ I η q x y /\ ξ ≈ rank y).

Definition rule (η : PSet) (l: Label) : PSet -> Prop :=
  match l with
  | a => RuleA η
  | b w => RuleB η w
  | c _ => fun _ => False
  end.
  
Lemma omega_not_succ {ζ : PSet} (h : omega ≈ succ ζ) : False.
Admitted.
(*  have ⟨n, e⟩ := mem_omega.1 ((mem_congr_right h).2 (mem_succ.2 (.inr (Equiv.refl ζ))))
  have h1 : succ ζ ∈ omega := mem_omega.2 ⟨n+1, succ_congr e⟩
  exact not_mem_self _ ((mem_congr_right h).1 h1)*)

(*! ### Invariance *)

(*variable {I}*)
Variable (I_resp : forall {η η' q q' x x' y y' : PSet},
  η ≈ η' -> q ≈ q' -> x ≈ x' -> y ≈ y' -> I η q x y -> I η' q' x' y').
(*include I_resp*)

Lemma Unb_resp {η η' q q' s s' : PSet} (eη : η ≈ η') (eq : q ≈ q') (es : s ≈ s')
    (h : Unb η q s) : Unb η' q' s'.
assert (back : forall {x y}, I η' q' x y -> I η q x y).
{intros ??; apply I_resp; try apply Equiv_refl; apply Equiv_symm; trivial. }
split;[|split].
*intros x y y' hx h1 h2.
 apply back in h1; apply back in h2.
 revert h1 h2; apply h.
 apply mem_congr_right with (1:=es); trivial.
*intros x y hx h1.
 apply back in h1.
 apply mem_congr_right with (1:=eη).
 revert h1; apply h.
 apply mem_congr_right with (1:=es); trivial.
*intros ζ hζ.
 apply (mem_congr_right eη) in hζ.
 destruct h as (_,(_,h)).
 destruct h with (1:=hζ) as (x & y & hx & h1 & h2).
 exists x; exists y; split; [|split]; trivial.
 +apply mem_congr_right with (1:=es); trivial.
 +revert h1; apply I_resp; trivial; apply Equiv_refl.
Qed.

Lemma Reach_resp {η η' ν ν' : PSet} (eη : η ≈ η') (eν : ν ≈ ν') (h : Reach η ν) :
    Reach η' ν'.
destruct h as (q & s & hq & hs & h).
exists q; exists s; split; [|split].
*apply mem_congr_right with (1:=eν); trivial.
*apply mem_congr_right with (1:=eν); trivial.
*revert h; apply Unb_resp; trivial; apply Equiv_refl.
Qed.

(*omit I_resp in*)
Lemma IsSucc_resp {η η' : PSet} (e : η ≈ η') (h : IsSucc η) : IsSucc η'.
Proof using I.
destruct h as (ζ, h).
exists ζ.
apply Equiv_trans with (1:=Equiv_symm e); trivial.
Qed.
                      
Lemma LimCase_resp {η η' : PSet} (e : η ≈ η') (h : LimCase η) : LimCase η'.
destruct h as (h1 & h2 & ν & hν & h3).
split; [|split;[|exists ν; split]].
*intro; apply h1.
 revert H; apply @IsSucc_resp; apply Equiv_symm; trivial.
*intro; apply h2.
 apply Equiv_trans with (1:=e); trivial.
*apply mem_congr_right with (1:=e); trivial.
*revert h3; apply Reach_resp; trivial.
 apply Equiv_refl.
Qed.

Lemma mem_Gν {η z : PSet} : z ∈ Gν η <-> z ∈ η /\ ~ Reach η z.
unfold Gν; rewrite mem_sep; [reflexivity|].
intros ?? e h h'; apply h.
revert h'; apply Reach_resp; [apply Equiv_refl|apply Equiv_symm; trivial].
Qed.

Lemma Gν_resp {η η' : PSet} (e : η ≈ η') : Gν η ≈ Gν η'.
apply ext; intro.
unfold Gν.
rewrite !@mem_sep.
*apply and_iff_morphism.
 apply mem_congr_right; trivial.
 apply not_iff_morphism.
 split; apply Reach_resp; try apply Equiv_refl; trivial.
 apply Equiv_symm; trivial.
*intros ?? e' nr r; apply nr.
 revert r; apply Reach_resp; [apply Equiv_refl|apply Equiv_symm;trivial].
*intros ?? e' nr r; apply nr.
 revert r; apply Reach_resp; [apply Equiv_refl|apply Equiv_symm;trivial].
Qed.

Lemma rule_resp {η η' : PSet} {l l' : Label} {ξ ξ' : PSet}
    (eη : η ≈ η') (el : Label_Equiv l l') (eξ : ξ ≈ ξ') (h : rule η l ξ) : rule η' l' ξ'.
Admitted.
(*cases el with
  | a =>
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl (eη.symm.trans (h.trans (succ_congr eξ)))
    · exact .inr (.inl ⟨eη.symm.trans h1, eξ.symm.trans h2⟩)
    · exact .inr (.inr ⟨h1.resp I_resp eη, eξ.symm.trans (h2.trans (Gν_resp I_resp eη))⟩)
  | b ew =>
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, q, s, x, y, h2, h3, h4, h5, h6⟩
    · exact .inl ⟨eη.symm.trans h1, (mem_congr_left (rank_congr ew)).1 h2,
        eξ.symm.trans (h3.trans (rank_congr ew))⟩
    · exact .inr ⟨h1.resp I_resp eη, q, s, x, y, ew.symm.trans h2,
        h3.resp I_resp eη (Equiv.refl _) (Equiv.refl _), h4,
        I_resp eη (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) h5, eξ.symm.trans h6⟩
  | c => exact h.elim*)

Lemma rule_func {η : PSet} {l : Label} {ξ ξ' : PSet}
    (h : rule η l ξ) (h' : rule η l ξ') : ξ ≈ ξ'.
Admitted.
(*cases l with
  | a =>
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with h' | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact succ_inj (h.symm.trans h')
    · exact (omega_not_succ (h1'.symm.trans h)).elim
    · exact (h1'.1 ⟨_, h⟩).elim
    · exact (omega_not_succ (h1.symm.trans h')).elim
    · exact h2.trans h2'.symm
    · exact (h1'.2.1 h1).elim
    · exact (h1.1 ⟨_, h'⟩).elim
    · exact (h1.2.1 h1').elim
    · exact h2.trans h2'.symm
  | b w =>
    rcases h with ⟨h1, -, h3⟩ | ⟨h1, q, s, x, y, h2, h3, h4, h5, h6⟩ <;>
      rcases h' with ⟨h1', -, h3'⟩ | ⟨h1', q', s', x', y', h2', -, -, h5', h6'⟩
    · exact h3.trans h3'.symm
    · exact (h1'.2.1 h1).elim
    · exact (h1.2.1 h1').elim
    · obtain ⟨eq, -, ex⟩ := triple_inj (h2.symm.trans h2')
      have h5'' := I_resp (Equiv.refl _) eq.symm ex.symm (Equiv.refl _) h5'
      exact h6.trans ((rank_congr (h3.1 x y y' h4 h5 h5'')).trans h6'.symm)
  | c => exact h.elim*)

(*! ### The class of the rule *)

(*variable (I) in*)
Definition Good (η : PSet) : Prop :=
  η ≈ empty \/ IsSucc η \/ η ≈ omega \/ exists ν, ν ∈ η /\ Reach η ν.

(*variable (I) in*)
(*- Ordinals all of whose predecessors, and itself, are handled by one of the cases. *)
Definition Cls (η : PSet) : Prop := IsOrd η /\ forall μ, (μ ∈ η \/ μ ≈ η) -> Good μ.

(*omit I_resp in*)
Lemma Cls_resp {η η' : PSet} (e : η ≈ η') (h : Cls η) : Cls η'.
Proof using I.
Admitted.
(*⟨h.1.resp e, fun μ hμ => h.2 μ (hμ.elim (fun h => .inl ((mem_congr_right e).2 h))
    (fun h => .inr (h.trans e.symm)))⟩*)

(*omit I_resp in*)
Lemma Cls_mem {η ξ : PSet} (h : Cls η) (hξ : ξ ∈ η) : Cls ξ.
Proof using I.  
Admitted.
(*⟨h.1.mem hξ, fun μ hμ => h.2 μ (.inl (hμ.elim (fun h' => h.1.trans ξ hξ μ h')
    (fun e => (mem_congr_left e).2 hξ)))⟩*)

(*omit I_resp in*)
Lemma succN_congr {G G' : PSet} (e : G ≈ G') : forall n, succN n G ≈ succN n G'.
Admitted.
(*| 0 => e
  | n+1 => succ_congr (succN_congr e n)*)

(*omit I_resp in*)
Lemma succN_empty {G : PSet} (e : G ≈ empty) : forall n, succN n G ≈ ofNat n.
Admitted.
(*  | 0 => e
  | n+1 => succ_congr (succN_empty e n)*)

Section em.
Hypothesis (em : forall p : Prop, p \/ ~p).

(*- In the limit case, the least `ν` is an element of `η` from which `η` is reached. *)
Lemma Gν_spec {η : PSet} (hη : IsOrd η) (h : LimCase η) :
  Gν η ∈ η /\ IsOrd (Gν η) /\ Reach η (Gν η).
Admitted.
(*  have up : forall {ν ν'}, ν' ∈ η -> ν ∈ ν' -> Reach I η ν -> Reach I η ν' :=
    fun hν' hν ⟨q, s, hq, hs, hu⟩ =>
      ⟨q, s, (hη.mem hν').trans _ hν _ hq, (hη.mem hν').trans _ hν _ hs, hu⟩
  have hG : IsOrd (Gν I η) := by
    refine ⟨fun μ hμ μ' hμ' => ?_, fun μ hμ => hη.mem_trans μ ((mem_Gν I_resp).1 hμ).1⟩
    have ⟨hμη, hμr⟩ := (mem_Gν I_resp).1 hμ
    have hμ'η := hη.trans μ hμη μ' hμ'
    exact (mem_Gν I_resp).2 ⟨hμ'η, fun h' => hμr (up hμη hμ' h')⟩
  have hmem : Gν I η ∈ η := by
    rcases hG.subset em hη (fun z hz => ((mem_Gν I_resp).1 hz).1) with h' | e
    · exact h'
    · have ⟨_, _, ν, hν, hr⟩ := h
      exact (((mem_Gν I_resp).1 ((mem_congr_right e).2 hν)).2 hr).elim
  refine ⟨hmem, hG, (em _).resolve_right fun hn => not_mem_self _ ((mem_Gν I_resp).2 ⟨hmem, hn⟩)⟩*)

Lemma rule_mem {η : PSet} {l : Label} {ξ : PSet} (hη : Cls η)
    (h : rule η l ξ) : ξ ∈ η /\ Cls ξ.
Admitted.
(*suffices ξ ∈ η from ⟨this, hη.mem this⟩
  cases l with
  | a =>
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (mem_congr_right h).2 (mem_succ.2 (.inr (Equiv.refl _)))
    · exact (mem_congr_right h1).2 (mem_omega.2 ⟨0, h2⟩)
    · exact (mem_congr_left h2).2 (Gν_spec I_resp em hη.1 h1).1
  | b w =>
    rcases h with ⟨h1, h2, h3⟩ | ⟨_, q, s, x, y, -, h3, h4, h5, h6⟩
    · exact (mem_congr_right h1).2 ((mem_congr_left h3).2 h2)
    · exact (mem_congr_left h6).2 (h3.2.1 x y h4 h5)
  | c => exact h.elim*)

Lemma rule_sup (U : PSet) {η G : PSet} (hη : Cls η)
    (hG : forall x, x ∈ G <-> exists ζ, rule η a ζ /\ x ∈ ζ) (x : PSet) :
  x ∈ η <-> exists l ξ, Avail D U G l /\ rule η l ξ /\ x ∈ succ ξ.
Admitted.
(*refine ⟨fun hx => ?_, fun ⟨l, ξ, _, hr, hx⟩ => ?_⟩
  rotate_left
  · have hξ := (rule_mem I_resp em hη hr).1
    rcases mem_succ.1 hx with hx | e
    · exact hη.1.trans ξ hξ x hx
    · exact (mem_congr_left e).2 hξ
  -- `G` is the target of the child `a`
  have hGa : forall {ζ}, rule I η .a ζ -> G ≈ ζ := fun {ζ} hζ => ext fun z =>
    (hG z).trans ⟨fun ⟨ζ', h1, h2⟩ => (mem_congr_right (rule_func I_resp h1 hζ)).1 h2,
      fun h => ⟨ζ, hζ, h⟩⟩
  rcases em (IsSucc η) with ⟨ζ, e⟩ | hs
  · exact ⟨.a, ζ, .inl rfl, .inl e, (mem_congr_right e).1 hx⟩
  rcases em (η ≈ omega) with hω | hω
  · have ⟨n, e⟩ := mem_omega.1 ((mem_congr_right hω).1 hx)
    have hGe : G ≈ empty := hGa (.inr (.inl ⟨hω, Equiv.refl _⟩))
    have hr : rank (ofNat n) ≈ ofNat n := (isOrd_ofNat n).rank_equiv
    have hw : ofNat n ∈ D G := mem_D_of_rank em (isOrd_empty.resp hGe.symm) (n+1)
      ((mem_congr_right (succN_empty hGe (n+1))).2
        ((mem_congr_left hr).2 (mem_succ.2 (.inr (Equiv.refl _)))))
    exact ⟨.b (ofNat n), rank (ofNat n), .inr (.inl ⟨_, hw, Label.Equiv.refl _⟩),
      .inl ⟨hω, (mem_congr_left hr).2 (mem_omega.2 ⟨n, Equiv.refl _⟩), Equiv.refl _⟩,
      mem_succ.2 (.inr (e.trans hr.symm))⟩
  have hL : LimCase I η := by
    rcases hη.2 η (.inr (Equiv.refl _)) with h | h | h | h
    · exact ((not_mem_empty x) ((mem_congr_right h).1 hx)).elim
    · exact (hs h).elim
    · exact (hω h).elim
    · exact ⟨hs, hω, h⟩
  obtain ⟨-, hGo, q, s, hq, hs', hu⟩ := Gν_spec I_resp em hη.1 hL
  have hGe : G ≈ Gν I η := hGa (.inr (.inr ⟨hL, Equiv.refl _⟩))
  have ⟨x', y, hx', hI, hxy⟩ := hu.2.2 x hx
  have hw : triple q s x' ∈ D G :=
    mem_D_of_rank em (hGo.resp hGe.symm) 4 <| (mem_congr_right (succN_congr hGe 4)).2 <|
      rank_triple_mem em hGo hq hs' (hGo.trans _ hs' _ (rank_mem hx'))
  exact ⟨.b (triple q s x'), rank y, .inr (.inl ⟨_, hw, Label.Equiv.refl _⟩),
    .inr ⟨hL, q, s, x', y, Equiv.refl _, hu, hx', hI, Equiv.refl _⟩, hxy⟩*)

(*- The definability rule meets the one-node conditions, for the class `Cls I`. *)
Lemma worldly_rule (U : PSet) : Rule D U rule Cls.
Admitted.
(*⟨rule_func I_resp, rule_resp I_resp, Cls.resp, rule_mem I_resp em,
   fun hη hG x => rule_sup I_resp em U hη hG x⟩*)

End em.

(*! ### The dichotomy *)

(*omit I_resp in
variable (I) in*)
(*- Either Replacement holds for every functional relation (any proposition, not only a
definable one), or there is an ordinal that is not `0`, not a successor, not `ω`, and into which
no `I`-definable function from parameters of smaller rank is cofinal. For first-order `I` the
latter is a worldly cardinal, and `V_ρ ⊨ ZF`. *)
Lemma dichotomy (em : forall p : Prop, p \/ ~p) :
    (forall (s : PSet) (φ : PSet -> PSet -> Prop),
      (forall {x x' y y'}, x ≈ x' -> y ≈ y' -> φ x y -> φ x' y') ->
      (forall {x y y'}, x ∈ s -> φ x y -> φ x y' -> y ≈ y') ->
      exists img : PSet, forall y, y ∈ img <-> exists x, x ∈ s /\ φ x y) \/
    exists ρ : PSet, IsOrd ρ /\ ~ ρ ≈ empty /\ ~ IsSucc ρ /\ ~ ρ ≈ omega /\
                       forall ν, ν ∈ ρ -> ~ Reach ρ ν.
destruct (em (exists ρ, IsOrd ρ /\ ~ Good ρ)) as [(ρ & hρ & hg) | hall ];
  [right|left].
*exists ρ; split; [trivial|split;[|split;[|split]]].
 +intros h; apply hg; left; trivial.
 +intros h; apply hg; right; left; trivial.
 +intros h; apply hg; right; right; left; trivial.
 +intros ν hν h; apply hg; do 3 right; exists ν; auto.
*intros s φ φ_resp φ_func.
 assert (good : forall η, IsOrd η -> Good η).
 {intros η hη.
  edestruct em as [h|h];[eassumption|].
  destruct hall; eauto. }
 assert (cls : forall η, IsOrd η -> Cls η).
 {intros η hη; split; [trivial|].
  intros μ hμ; apply good.
  destruct hμ as [h|e];
    [eapply IsOrd_mem with (1:=hη)
    |revert hη;apply IsOrd_resp; apply Equiv_symm]; trivial. }
 (*-- the ranks of the values*)
 pose (ψ (*: PSet -> PSet -> Prop*) := fun x η => exists y, φ x y /\ η ≈ rank y).
 edestruct @Rule.replacement with (1:=worldly_rule em s) (s:=s) (φ:=ψ) as (R, hR);
   trivial.
 {intros ???? ex eη (y & h1 & h2); exists y; split.
  *revert h1; apply φ_resp; [trivial|apply Equiv_refl].
  *apply Equiv_trans with (2:=h2).
   apply Equiv_symm; trivial. }
 {intros ??? hx (y & h1 & h2) (y' & h1' & h2').
  apply Equiv_trans with (1:=h2).
  apply Equiv_trans with (2:=Equiv_symm h2').
  apply rank_congr.
  revert h1 h1'; apply φ_func; trivial. }
 {intros ??? (y & ? & h2).
  apply cls.
  apply Equiv_symm in h2.
  apply IsOrd_resp with (1:=h2).
  apply isOrd_rank. }
 pose (p (*: PSet -> Prop*) := fun y => exists x, x ∈ s /\ φ x y).
 exists  (sep p (Vl R)); intros y.
 rewrite mem_sep.
 2:{intros z z' e (x & hx & h).
    exists x; split; [trivial|].
    revert h; apply φ_resp; [apply Equiv_refl|trivial]. }
 split; [destruct 1; trivial|].
 intros h; split; [|trivial].
 destruct h as (x & hx & hφ).
   assert (hr : rank y ∈ R).
 {apply hR.
  exists x; split; [trivial|].
  exists y; split; [trivial|].
  apply Equiv_refl. }
 apply (mem_Vl em).
 eapply mem_congr_left; [|eapply rank_mem; eassumption].
 apply Equiv_symm; apply IsOrd_rank_equiv.
 apply  (isOrd_rank y).
Qed.

End S.

Print Assumptions dichotomy.
