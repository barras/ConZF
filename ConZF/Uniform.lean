import ConZF.FirstOrder
/-!
One model, with no case distinction in its definition: the class `HG` of the sets whose rank is
*hereditarily good*, that is, every ordinal up to the rank is `0`, a successor, `ω`, or reachable
by the definability rule. If every ordinal is good this is the class of all sets, and otherwise
it is `V_ρ` for the least ordinal `ρ` that is not good; but neither the disjunction nor `ρ` is
needed to define the model or to state that it satisfies `ZF`.
-/
universe u

namespace PSet
open Fml

/-- The sets of hereditarily good rank. -/
def HG (x : PSet.{u}) : Prop := Cls ISat (rank x)

section
variable (em : ∀ p : Prop, p ∨ ¬p)
include em

omit em in
theorem Cls.succ {I} {η : PSet.{u}} (h : Cls I η) : Cls I (succ η) :=
  ⟨h.1.succ, fun μ hμ => hμ.elim
    (fun hm => h.2 μ (mem_succ.1 hm))
    (fun e => .inr (.inl ⟨η, e⟩))⟩

omit em in
theorem cls_empty {I} : Cls I empty.{u} :=
  ⟨isOrd_empty, fun _ hμ => hμ.elim (fun h => (not_mem_empty _ h).elim) .inl⟩

omit em in
theorem cls_omega {I} : Cls I omega.{u} := by
  refine ⟨isOrd_omega, fun μ hμ => hμ.elim (fun h => ?_) (fun e => .inr (.inr (.inl e)))⟩
  have ⟨n, e⟩ := mem_omega.1 h
  cases n with
  | zero => exact .inl e
  | succ n => exact .inr (.inl ⟨_, e⟩)

/-- A set whose elements have ranks below a hereditarily good `R` is in the model. -/
theorem HG.of_bound {y R : PSet.{u}} (hR : Cls ISat R) (h : ∀ z, z ∈ y → rank z ∈ R) : HG y :=
  (Cls.succ hR).mem (rank_mem_succ em hR.1 h)

omit em in
theorem HG.mem {x z : PSet.{u}} (hx : HG x) (hz : z ∈ x) : HG z := Cls.mem hx (rank_mem hz)

omit em in
theorem HG.resp {x x' : PSet.{u}} (e : x ≈ x') (hx : HG x) : HG x' := Cls.resp (rank_congr e) hx

theorem hg_model : ZFModel HG.{u} := by
  refine ⟨fun hx hz => hx.mem hz, ?_, fun {x y} hx hy => ?_, fun {x} hx => ?_,
    fun {x} hx => ?_, ?_, fun P x hx => ?_, fun ψ e he a ha hf => ?_⟩
  · exact HG.of_bound em cls_empty fun _ h => (not_mem_empty _ h).elim
  · -- pairs: compare the two ranks
    have key : ∀ {x y : PSet.{u}}, HG x → (∀ z, z ∈ rank y → z ∈ rank x) → HG (upair x y) :=
      fun {x y} hx hsub => HG.of_bound em (Cls.succ hx) fun z hz => (mem_upair.1 hz).elim
        (fun e => mem_succ.2 (.inr (rank_congr e)))
        (fun e => mem_succ.2 (((isOrd_rank y).subset em hx.1 hsub).imp
          (fun h => (mem_congr_left (rank_congr e)).2 h) (fun h => (rank_congr e).trans h)))
    rcases (isOrd_rank x).trichotomy em (isOrd_rank y) with h | h | h
    · exact (key hy fun z hz => (isOrd_rank y).trans _ h z hz).resp
        (ext fun z => mem_upair.trans (Or.comm.trans mem_upair.symm))
    · exact key hx fun z hz => (mem_congr_right h).2 hz
    · exact key hx fun z hz => (isOrd_rank x).trans _ h z hz
  · exact HG.of_bound em hx fun z hz =>
      have ⟨w, hw, hzw⟩ := mem_sUnion.1 hz
      (isOrd_rank _).trans _ (rank_mem hw) _ (rank_mem hzw)
  · exact HG.of_bound em (Cls.succ hx) fun z hz =>
      rank_mem_succ em (isOrd_rank _) fun w hw => rank_mem (mem_powerset.1 hz w hw)
  · exact Cls.resp isOrd_omega.rank_equiv.symm cls_omega
  · exact HG.of_bound em hx fun _ ⟨⟨i, _⟩, e⟩ => rank_mem ⟨i, e⟩
  -- Replacement. First the ranks of the values are bounded, by the materializing recursion.
  let φ : PSet.{u} → PSet.{u} → Prop := fun x η =>
    ∃ y, HG y ∧ Sat HG ψ (Env.cons x (Env.cons y e)) ∧ η ≈ rank y
  have ⟨R, hR⟩ := (worldly_rule (ISat_resp em) em a).replacement a rfl φ
    (fun ex eη ⟨y, h1, h2, h3⟩ => ⟨y, h1,
      Sat.resp ψ (Env.cons_resp ex fun _ => Equiv.refl _) h2, eη.symm.trans h3⟩)
    (fun hx ⟨y, h1, h2, h3⟩ ⟨y', h1', h2', h3'⟩ =>
      h3.trans ((rank_congr (hf _ y y' hx h1 h1' h2 h2')).trans h3'.symm))
    (fun _ ⟨y, h1, _, h3⟩ => Cls.resp h3.symm h1)
  -- `θ` is the strict supremum of those ranks
  let θ := rank R
  have hθo : IsOrd θ := isOrd_rank R
  have val : ∀ {x y}, x ∈ a → HG y → Sat HG ψ (Env.cons x (Env.cons y e)) → rank y ∈ θ :=
    fun {x y} hx hy h => (mem_congr_left (isOrd_rank y).rank_equiv).1
      (rank_mem ((hR (rank y)).2 ⟨x, hx, y, hy, h, Equiv.refl _⟩))
  have below : ∀ μ, μ ∈ θ → Cls ISat μ := by
    intro μ hμ
    have ⟨η, hη, hμ⟩ := mem_rank'.1 hμ
    have ⟨_, _, y, hy, _, e⟩ := (hR η).1 hη
    have hc : Cls ISat (rank η) := Cls.resp ((rank_congr e).trans (isOrd_rank y).rank_equiv).symm hy
    exact (mem_succ.1 hμ).elim (fun h => hc.mem h) (fun e => hc.resp e.symm)
  have inVl : ∀ {y}, rank y ∈ θ → y ∈ Vl θ := fun h =>
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
    have hr : ∀ ν, ν ∈ θ → ¬ Reach ISat θ ν := fun ν hν h => hg (.inr (.inr (.inr ⟨ν, hν, h⟩)))
    have top : ∀ x, HG x ↔ x ∈ Vl θ := fun x => by
      refine ⟨fun hx => inVl ?_, fun hx => below _
        ((mem_congr_right hθo.rank_equiv).1 ((mem_Vl em).1 hx))⟩
      rcases hx.1.trichotomy em hθo with h | h | h
      · exact h
      · exact (hg (hx.2 θ (.inr h.symm))).elim
      · exact (hg (hx.2 θ (.inl h))).elim
    have sat : ∀ {E}, Sat HG ψ E ↔ Sat (· ∈ Vl θ) ψ E :=
      Sat.resp_iff top ψ fun _ => Equiv.refl _
    have ⟨b, hb, hb'⟩ := (Vl_model em hθo h0 hs hω hr).repl ψ e (fun i => (top _).1 (he i)) a
      ((top a).1 ha) fun x y y' hx hy hy' h1 h2 =>
        hf x y y' hx ((top y).2 hy) ((top y').2 hy') (sat.2 h1) (sat.2 h2)
    exact ⟨b, (top b).2 hb, fun x y hx hy h => hb' x y hx ((top y).1 hy) (sat.1 h)⟩

/-- The consistency of `ZF`, by the single model `HG`. -/
theorem con_ZF' : Con ZF := (hg_model.{0} em).con em

end

/-- info: 'PSet.con_ZF'' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZF'
