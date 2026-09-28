Require Import PSet Pair Ord VLevel Worldly Fml Proof FirstOrder ZF.
(*!
One model, with no case distinction in its definition: the class `HG` of the sets whose rank is
*hereditarily good*, that is, every ordinal up to the rank is `0`, a successor, `ω`, or reachable
by the definability rule. If every ordinal is good this is the class of all sets, and otherwise
it is `V_ρ` for the least ordinal `ρ` that is not good; but neither the disjunction nor `ρ` is
needed to define the model or to state that it satisfies `ZF`.
*)

(*- The sets of hereditarily good rank. *)
Definition HG (x : PSet) : Prop := Cls ISat (rank x).

Lemma isL_HG x : isL(HG x).
  unfold HG;prove_isL.
Qed.
Hint Resolve isL_HG : core.

Lemma Cls_succ {I} {η : PSet} (h : Cls I η) : Cls I (succ η).
destruct h as (ho,hc).
split; [apply IsOrd_succ; trivial|].
destruct 1 as [hm|e].
*apply mem_succ in hm.
 Telim hm; auto.
*Tright; left; red; eauto.
Qed.

Lemma cls_empty {I} : Cls I empty.
split; [apply isOrd_empty|].
destruct 1; [|Tleft; trivial].
apply not_mem_empty in H; contradiction.
Qed.

Lemma cls_omega {I} : Cls I omega.
split; [apply isOrd_omega|].
destruct 1 as [h|e].
*apply mem_omega in h; Tdestruct h as (n,e).
 destruct n; [Tleft; trivial|].
simpl in e.
 Tright; left; red; eauto.
*Tright; right; left; trivial.
Qed.
  
Section S.
Hypothesis (em : forall p : Prop, #(p \/ ~p)).

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
  intros z; rewrite mem_upair; Tintros [e|e].
  +apply mem_succ; Tright; apply rank_congr; trivial.
  +apply rank_congr in e.
   apply mem_congr_left with (1:=e).
   apply mem_succ.
   eapply IsOrd_subset with (1:=em) (2:=isOrd_rank _) (3:=isOrd_rank _).
   trivial. }
 Tdestruct (IsOrd_trichotomy em (isOrd_rank x) (isOrd_rank y))
   as [h|[h|h]].
 +apply @HG_resp with (upair y x).
  {apply ext; intros z; do 2 rewrite mem_upair; apply Tr_morph; apply or_comm. }
  apply key; trivial.
  intros z hz; eapply (@IsOrd_trans _ (isOrd_rank y) _); eauto.
 +apply key; trivial.
  intros z hz; apply mem_congr_right with (1:=h); trivial.
 +apply key; trivial.
  intros z hz; eapply (@IsOrd_trans _ (isOrd_rank x) _); eauto.
*intros ? hx.
 apply HG_of_bound with (1:=hx).
 intros z; rewrite mem_sUnion; Tintros (w & hw & hzw).
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
 intros ?; Tintros ((i,?),e); simpl in e.
 apply rank_mem; Texists i; trivial.
* (*-- Replacement. First the ranks of the values are bounded, by the materializing recursion.*)
 intros ψ e he a ha hf.
 pose (φ := fun x η =>
              exists y, HG y /\ Sat HG ψ (Env_cons x (Env_cons y e)) /\
                          η ≈ rank y).
 assert (Rl := worldly_rule _ (@ISat_resp em) em a).
 Tdestruct (@Rule.replacement _ _ _ _ Rl _ (reflexivity _) φ) as (R, hR); trivial.
 2:{intros ???? ex eη (y & h1 & h2 & h3).
  exists y; split; [trivial|split].
  *apply @Sat_resp with (2:=h2).
   intros; apply Env_cons_resp; trivial.
   intros; apply Equiv_refl.
  *apply Equiv_trans with (2:=h3).
   apply Equiv_symm; trivial. }
 2:{intros ??? hx (y & h1 & h2 & h3) (y' & h1' & h2' & h3').
  apply Equiv_trans with (1:=h3).
  apply Equiv_trans with (2:=Equiv_symm h3').
  apply rank_congr.
  apply hf with x; trivial. }
 2:{intros ?? ? (y & h1 & ? & h3).
  eapply Cls_resp with (1:=Equiv_symm h3); trivial. }
 (*-- `θ` is the strict supremum of those ranks*)
 pose (θ := rank R).
 assert (hθo (*: IsOrd θ*) := isOrd_rank R).
 assert (val : forall {x y}, x ∈ a -> HG y -> Sat HG ψ (Env_cons x (Env_cons y e)) -> rank y ∈ θ).
 {intros ?? hx hy h.
  apply mem_congr_left with (1:=IsOrd_rank_equiv(isOrd_rank y)).
  apply rank_mem.
  apply hR.
  Texists x; split; trivial.
  exists y; split; [|split]; trivial.
  apply Equiv_refl. }
 assert (below : forall μ, μ ∈ θ -> Cls ISat μ).
 {intros μ hμ.
  apply mem_rank' in hμ; Tdestruct hμ as (η & hη & hμ).
  rewrite hR in hη; Tdestruct hη as (?& ?& y& hy& ?& e').
  assert (hc : Cls ISat (rank η)).
  {revert hy; apply Cls_resp.
   apply rank_congr in e'.
   apply Equiv_trans with (2:=Equiv_symm e').
   apply Equiv_symm; apply IsOrd_rank_equiv.
   apply isOrd_rank. }
  apply mem_succ in hμ; Tdestruct hμ as [h|e''].
  *apply Cls_mem with (2:=h); trivial.
  *revert hc; apply Cls_resp; apply Equiv_symm; trivial. }
 assert (inVl : forall {y}, rank y ∈ θ -> y ∈ Vl θ).
 {intros ?; rewrite (mem_Vl em).
  apply mem_congr_right.
  apply IsOrd_rank_equiv; trivial. }
 Tdestruct (em (Good ISat θ)) as [hg | hg].
 +(*-- `θ` is hereditarily good, and `V_θ` is in the model*)
  assert (hθ : Cls ISat θ).
  {split; [trivial|].
   intros μ [h|e']; [apply (below μ h); right; apply Equiv_refl|].
   assert (em' := em).
   Tdestruct em' as [?|hn]; [eassumption|].
   Tdestruct hg as [h | [h | [h | (ν& hν& h)]]].
   *Tleft; apply Equiv_trans with (1:=e')(2:=h).
   *Tdestruct h as (ζ, h).
    Tright; left; Texists ζ; apply Equiv_trans with (1:=e')(2:=h).
   *Tright; right; left; apply Equiv_trans with (1:=e')(2:=h).
   *Tright; do 2 right; exists ν.
    split; [apply mem_congr_right with (1:=e'); trivial|].
    revert h; apply Reach_resp with (1:=@ISat_resp em);
      [apply Equiv_symm; trivial|apply Equiv_refl]. }
  Texists (Vl θ); split.
  ++apply HG_of_bound with (1:=hθ).
    intros z hz.
    rewrite (mem_Vl em) in hz.
    revert hz; apply mem_congr_right; apply Equiv_symm.
    apply IsOrd_rank_equiv; trivial.
  ++intros x y hx hy h; apply inVl; eauto.
 +(*-- otherwise the model is `V_θ`, and `θ` is not reachable *)
  assert (h0 : ~ θ ≈ empty).
  {intro h; apply hg; Tleft; trivial. }
  assert (hs : ~ IsSucc θ).
  {intro h; apply hg; Tright; left; trivial. }
  assert (hω : ~ θ ≈ omega).
  {intro h; apply hg; Tright;  right; left; trivial. }
  assert (hr : forall ν, ν ∈ θ -> ~ Reach ISat θ ν).
  {intros ν hν h; apply hg; Tright; do 2 right; exists ν; auto. }
  assert (top : forall x, HG x <-> x ∈ Vl θ).
  {intros x; split.
   *intros hx; apply inVl.
    Tdestruct (IsOrd_trichotomy em (proj1 hx) hθo) as [h | [h | h]]; trivial.
    +destruct hg; apply hx; right.
     apply Equiv_symm; trivial.
    +destruct hg; apply hx; left; trivial.
   *intros hx; apply below.
    rewrite (mem_Vl em) in hx.
    revert hx; apply mem_congr_right; apply Equiv_symm.
    apply IsOrd_rank_equiv; trivial. }
  assert (sat : forall {E}, Sat HG ψ E <-> Sat (fun x=>x ∈ Vl θ) ψ E).
  {intros E; apply Sat_resp_iff with (1:=top); intros; apply Equiv_refl. }
  assert (Mrepl := @M_repl _ (Vl_model em hθo h0 hs hω hr)).
  Tdestruct (fun hyp => Mrepl ψ e hyp a) as (b & hb & hb').
  Texists b; split; [apply top; trivial|].
  intros x y hx hy h.
  apply sat in h.
  apply hb' with x; trivial.
  apply top; trivial.
  {intros i; apply top; auto. }
  {apply top; auto. }
  {intros x y y' hx hy hy' h1 h2.
   apply sat in h1; apply sat in h2.
   revert h1 h2.
   apply hf; trivial; apply top; trivial. }
Qed.

End S.

(*- The consistency of `ZF`, by the single model `HG`. *)
Theorem con_ZF' (em : forall p : Prop, #(p \/ ~p)) : Con ZF.
apply con with (2:=em) (1:=hg_model em).
Qed.

(*- info: 'PSet.con_ZF'' does not depend on any axioms *)
Print Assumptions con_ZF'.
