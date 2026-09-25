Require Import PSet Pair Ord VLevel Worldly Fml FirstOrder ZF.
(*!
One model, with no case distinction in its definition: the class `HG` of the sets whose rank is
*hereditarily good*, that is, every ordinal up to the rank is `0`, a successor, `ω`, or reachable
by the definability rule. If every ordinal is good this is the class of all sets, and otherwise
it is `V_ρ` for the least ordinal `ρ` that is not good; but neither the disjunction nor `ρ` is
needed to define the model or to state that it satisfies `ZF`.
*)

(*- The sets of hereditarily good rank. *)
Definition HG (x : PSet) : Prop := Cls ISat (rank x).

Lemma Cls_succ {I} {η : PSet} (h : Cls I η) : Cls I (succ η).
destruct h as (ho,hc).
split; [apply IsOrd_succ; trivial|].
destruct 1 as [hm|e].
*apply hc.
 apply mem_succ; trivial.
*right; left; red; eauto.
Qed.

Lemma cls_empty {I} : Cls I empty.
split; [apply isOrd_empty|].
destruct 1; [|left; trivial].
apply not_mem_empty in H; contradiction.
Qed.

Lemma cls_omega {I} : Cls I omega.
split; [apply isOrd_omega|].
destruct 1 as [h|e].
*apply mem_omega in h; destruct h as (n,e).
 destruct n; [left; trivial|].
simpl in e.
 right; left; red; eauto.
*right; right; left; trivial.
Qed.
  
Section S.
Hypothesis (em : forall p : Prop, p \/ ~p).

(*- A set whose elements have ranks below a hereditarily good `R` is in the model. *)
Lemma HG_of_bound {y R : PSet} (hR : Cls ISat R) (h : forall z, z ∈ y -> rank z ∈ R) : HG y.
apply Cls_mem with (1:=Cls_succ hR).
apply rank_mem_succ; trivial.
apply hR.
Qed.

Lemma HG_mem {x z : PSet} (hx : HG x) (hz : z ∈ x) : HG z.
apply Cls_mem with (1:=hx).
apply rank_mem; trivial.
Qed.

Lemma HG_resp {x x' : PSet} (e : x ≈ x') (hx : HG x) : HG x'.
revert hx; apply Cls_resp.
apply rank_congr; trivial.
Qed.

Lemma hg_model : ZFModel HG.
split.
*intros ?? hx hz; eauto using HG_mem.
*eapply HG_of_bound with (1:=cls_empty).
 intros ? h; apply not_mem_empty in h; contradiction.
*(* -- pairs: compare the two ranks*)
 intros x y hx hy.
 assert (key : forall {x y : PSet}, HG x -> (forall z, z ∈ rank y -> z ∈ rank x) -> HG (upair x y)).
 {clear -em.
  intros x y hx hsub; eapply HG_of_bound with (1:=Cls_succ hx).
  intros z; rewrite mem_upair; destruct 1 as [e|e].
  +apply mem_succ; right; apply rank_congr; trivial.
  +apply rank_congr in e.
   apply mem_congr_left with (1:=e).
   apply mem_succ.
   eapply IsOrd_subset with (1:=em) (2:=isOrd_rank _) (3:=isOrd_rank _).
   trivial. }
 destruct IsOrd_trichotomy with (1:=em)(2:=isOrd_rank x)(3:=isOrd_rank y)
   as [h|[h|h]].
 +apply @HG_resp with (upair y x).
  {apply ext; intros z; do 2 rewrite mem_upair; apply or_comm. }
  apply key; trivial.
  intros z hz; eapply (@IsOrd_trans _ (isOrd_rank y) _); eauto.
 +apply key; trivial.
  intros z hz; apply mem_congr_right with (1:=h); trivial.
 +apply key; trivial.
  intros z hz; eapply (@IsOrd_trans _ (isOrd_rank x) _); eauto.
*intros ? hx.
 apply HG_of_bound with (1:=hx).
 intros z; rewrite mem_sUnion; intros (w & hw & hzw).
 eapply (@IsOrd_trans _ (isOrd_rank x) _); eapply rank_mem; eassumption.
*intros ? hx.
 apply HG_of_bound with (1:=Cls_succ hx).
 intros z hz.
 apply rank_mem_succ with (1:=em) (2:=isOrd_rank _).
 intros w hw; apply rank_mem; trivial.
 rewrite mem_powerset in hz; auto.
*apply Cls_resp with (2:=cls_omega).
 apply Equiv_symm.
 apply IsOrd_rank_equiv.
 apply isOrd_omega.
*intros P x hx.
 apply HG_of_bound with (1:=hx).
 intros ? ((i,?),e); simpl in e.
 apply rank_mem; exists i; trivial.
* (*-- Replacement. First the ranks of the values are bounded, by the materializing recursion.*)
 intros ψ e he a ha hf.
 pose (φ := fun x η =>
              exists y, HG y /\ Sat HG ψ (Env_cons x (Env_cons y e)) /\
                          η ≈ rank y).
 assert (Rl := worldly_rule _ (@ISat_resp em) em a).
 destruct @Rule.replacement with (1:=Rl) (s:=a) (φ:=φ) as (R, hR); trivial.
 {intros ???? ex eη (y & h1 & h2 & h3).
  exists y; split; [trivial|split].
  *apply @Sat_resp with (2:=h2).
   intros; apply Env_cons_resp; trivial.
   intros; apply Equiv_refl.
  *apply Equiv_trans with (2:=h3).
   apply Equiv_symm; trivial. }
 {intros ??? hx (y & h1 & h2 & h3) (y' & h1' & h2' & h3').
  apply Equiv_trans with (1:=h3).
  apply Equiv_trans with (2:=Equiv_symm h3').
  apply rank_congr.
  apply hf with x; trivial. }
 {intros ?? ? (y & h1 & ? & h3).
  eapply Cls_resp with (1:=Equiv_symm h3); trivial. }
 (*-- `θ` is the strict supremum of those ranks*)
 pose (θ := rank R).
 assert (hθo (*: IsOrd θ*) := isOrd_rank R).
 assert (val : forall {x y}, x ∈ a -> HG y -> Sat HG ψ (Env_cons x (Env_cons y e)) -> rank y ∈ θ).
 {intros ?? hx hy h.
  apply mem_congr_left with (1:=IsOrd_rank_equiv(isOrd_rank y)).
  apply rank_mem.
  apply hR.
  exists x; split; trivial.
  exists y; split; [|split]; trivial.
  apply Equiv_refl. }
 assert (below : forall μ, μ ∈ θ -> Cls ISat μ).
Admitted.
(*intro μ hμ
    have ⟨η, hη, hμ⟩ := mem_rank'.1 hμ
    have ⟨_, _, y, hy, _, e⟩ := (hR η).1 hη
    have hc : Cls ISat (rank η) := Cls.resp ((rank_congr e).trans (isOrd_rank y).rank_equiv).symm hy
    exact (mem_succ.1 hμ).elim (fun h => hc.mem h) (fun e => hc.resp e.symm)
  have inVl : forall {y}, rank y ∈ θ -> y ∈ Vl θ := fun h =>
    (mem_Vl em).2 ((mem_congr_right hθo.rank_equiv).2 h)
  rcases em (Good ISat θ) with hg | hg
  · -- `θ` is hereditarily good, and `V_θ` is in the model
    have hθ : Cls ISat θ := ⟨hθo, fun μ hμ => hμ.elim (fun h => (below μ h).2 μ (.inr (Equiv.refl _)))
      (fun e => (em (Good ISat μ)).resolve_right fun hn => hn <| by
        rcases hg with h | ⟨ζ, h⟩ | h | ⟨ν, hν, h⟩
        · exact .inl (e.trans h)
        · exact .inr (.inl ⟨ζ, e.trans h⟩)
        · exact .inr (.inr (.inl (e.trans h)))
        · exact .inr (.inr (.inr ⟨ν, (mem_congr_right e).2 hν,
            h.resp (ISat_resp em) e.symm (Equiv.refl _)⟩)))⟩
    refine ⟨Vl θ, HG.of_bound em hθ fun z hz =>
      (mem_congr_right hθo.rank_equiv).1 ((mem_Vl em).1 hz), fun x y hx hy h => inVl (val hx hy h)⟩
  · -- otherwise the model is `V_θ`, and `θ` is not reachable
    have h0 : ¬ θ ≈ empty := fun h => hg (.inl h)
    have hs : ¬ IsSucc θ := fun h => hg (.inr (.inl h))
    have hω : ¬ θ ≈ omega := fun h => hg (.inr (.inr (.inl h)))
    have hr : forall ν, ν ∈ θ -> ¬ Reach ISat θ ν := fun ν hν h => hg (.inr (.inr (.inr ⟨ν, hν, h⟩)))
    have top : forall x, HG x <-> x ∈ Vl θ := fun x => by
      refine ⟨fun hx => inVl ?_, fun hx => below _
        ((mem_congr_right hθo.rank_equiv).1 ((mem_Vl em).1 hx))⟩
      rcases hx.1.trichotomy em hθo with h | h | h
      · exact h
      · exact (hg (hx.2 θ (.inr h.symm))).elim
      · exact (hg (hx.2 θ (.inl h))).elim
    have sat : forall {E}, Sat HG ψ E <-> Sat (· ∈ Vl θ) ψ E :=
      Sat.resp_iff top ψ fun _ => Equiv.refl _
    have ⟨b, hb, hb'⟩ := (Vl_model em hθo h0 hs hω hr).repl ψ e (fun i => (top _).1 (he i)) a
      ((top a).1 ha) fun x y y' hx hy hy' h1 h2 =>
        hf x y y' hx ((top y).2 hy) ((top y').2 hy') (sat.2 h1) (sat.2 h2)
    exact ⟨b, (top b).2 hb, fun x y hx hy h => hb' x y hx ((top y).1 hy) (sat.1 h)⟩
 *)

(*- The consistency of `ZF`, by the single model `HG`. *)
Lemma con_ZF' : Con ZF.
apply con with (2:=em) (1:=hg_model).
Qed.

End S.

(*- info: 'PSet.con_ZF'' does not depend on any axioms *)
Print Assumptions con_ZF'.
