import ConZF.Repl
/-
A sanity check that the hypotheses of `PSet.replacement` are satisfiable: the class of finite
ordinals has uniformly defined coherent assignments (a chain of `a`-children), for every `D`
and every parameter set. The resulting instance of Replacement is of no interest in itself,
the image being a subset of `ω`; the point is that `Coherent` is not vacuous and that the
clauses `desc`, `sup`, `IsG` are exercised with a nonempty `G`.
-/
universe u

namespace PSet

theorem mem_asymm : ∀ (x : PSet.{u}) {y}, y ∈ x → ¬ x ∈ y := by
  intro x
  induction x using mem_induction with | _ x ih => ?_
  intro y hy hx
  exact ih y hy hx hy

theorem succ_inj {t t' : PSet.{u}} (h : succ t ≈ succ t') : t ≈ t' := by
  have h1 : t ∈ succ t' := (mem_congr_right h).1 (mem_succ.2 (.inr (Equiv.refl _)))
  have h2 : t' ∈ succ t := (mem_congr_right h).2 (mem_succ.2 (.inr (Equiv.refl _)))
  rcases mem_succ.1 h1 with h1 | h1
  · rcases mem_succ.1 h2 with h2 | h2
    · exact (mem_asymm _ h1 h2).elim
    · exact h2.symm
  · exact h1

inductive IsNat : PSet.{u} → Prop
  | zero {t} : t ≈ empty → IsNat t
  | succ {t t'} : IsNat t' → t ≈ succ t' → IsNat t

theorem IsNat.resp {t t' : PSet.{u}} (h : IsNat t) (e : t ≈ t') : IsNat t' := by
  cases h with
  | zero h => exact .zero (e.symm.trans h)
  | succ h h' => exact .succ h (e.symm.trans h')

theorem IsNat.pred {t t' : PSet.{u}} (h : IsNat t) (e : t ≈ PSet.succ t') : IsNat t' := by
  cases h with
  | zero h =>
    exact (not_mem_empty _ ((mem_congr_right (e.symm.trans h)).1
      (mem_succ.2 (.inr (Equiv.refl t'))))).elim
  | succ h h' => exact h.resp (succ_inj (h'.symm.trans e))

/-- `Chain η k t`: `t` is the `k`-th predecessor of `η`. -/
inductive Chain (η : PSet.{u}) : Nat → PSet.{u} → Prop
  | zero {t} : η ≈ t → Chain η 0 t
  | succ {k t t'} : Chain η k t → t ≈ succ t' → Chain η (k+1) t'

theorem Chain.func {η : PSet.{u}} {k t t'} (h : Chain η k t) (h' : Chain η k t') : t ≈ t' := by
  induction h generalizing t' with
  | zero e => cases h' with | zero e' => exact e.symm.trans e'
  | succ _ e ih => cases h' with | succ h' e' => exact succ_inj (e.symm.trans ((ih h').trans e'))

theorem Chain.resp {η : PSet.{u}} {k t t'} (h : Chain η k t) (e : t ≈ t') : Chain η k t' := by
  cases h with
  | zero h => exact .zero (h.trans e)
  | succ h h' => exact .succ h (h'.trans (equiv_iff_mem.2 fun _ => mem_succ_congr e))

theorem Chain.resp_left {η η' : PSet.{u}} {k t} (e : η ≈ η') (h : Chain η k t) : Chain η' k t := by
  induction h with
  | zero h => exact .zero (e.symm.trans h)
  | succ _ h' ih => exact .succ ih h'

theorem Chain.isNat {η : PSet.{u}} {k t} (h : Chain η k t) (hη : IsNat η) : IsNat t := by
  induction h with
  | zero e => exact hη.resp e
  | succ _ e ih => exact ih.pred e

/-- The canonical assignment for a finite ordinal `η`: the path `a^k` has target the `k`-th
predecessor of `η`. -/
def NatT (η : PSet.{u}) (p : Path.{u}) (t : PSet.{u}) : Prop :=
  ∃ k, p = List.replicate k .a ∧ Chain η k t

theorem natT_cons {η : PSet.{u}} {l p t} (h : NatT η (l :: p) t) :
    l = .a ∧ ∃ k, p = List.replicate k .a ∧ Chain η (k+1) t := by
  obtain ⟨k, e, h⟩ := h
  cases k with
  | zero => cases e
  | succ k =>
    rw [List.replicate_succ] at e
    cases e
    exact ⟨rfl, k, rfl, h⟩

theorem natT_coherent (D : PSet.{u} → PSet.{u}) (U η : PSet.{u}) (hη : IsNat η) :
    Coherent D U (NatT η) ∧ NatT η [] η := by
  refine ⟨?_, 0, rfl, .zero (Equiv.refl _)⟩
  have same : ∀ {k k' : Nat}, List.replicate k Label.a.{u} = List.replicate k' .a → k = k' :=
    fun e => by simpa using congrArg List.length e
  constructor
  · rintro _ t t' ⟨k, rfl, h⟩ e
    exact ⟨k, rfl, h.resp e⟩
  · rintro _ t t' ⟨k, rfl, h⟩ ⟨k', e, h'⟩
    cases same e
    exact h.func h'
  · rintro l l' p t e h
    obtain ⟨rfl, k, rfl, hc⟩ := natT_cons h
    cases e
    exact ⟨k+1, rfl, hc⟩
  · rintro l p t t' h ⟨k', e', h'⟩
    obtain ⟨rfl, k, rfl, hc⟩ := natT_cons h
    cases same e'
    cases hc with | succ hc e =>
    exact (mem_congr_right ((hc.func h').symm.trans e).symm).1 (mem_succ.2 (.inr (Equiv.refl _)))
  · rintro _ t G ⟨k, rfl, h⟩ - x
    constructor
    · intro hx
      cases h.isNat hη with
      | zero e => exact (not_mem_empty _ ((mem_congr_right e).1 hx)).elim
      | succ _ e => exact ⟨.a, _, .inl rfl, ⟨k+1, rfl, .succ h e⟩, (mem_congr_right e).1 hx⟩
    · rintro ⟨l, t', -, h', hx⟩
      obtain ⟨rfl, k', e', hc⟩ := natT_cons h'
      cases same e'
      cases hc with | succ hc e =>
      exact (mem_congr_right ((h.func hc).trans e)).2 hx

/-- Replacement for functional relations with finite ordinal values, through the recursion. -/
theorem replacement_nat (D : PSet.{u} → PSet.{u}) (s : PSet.{u}) (φ : PSet.{u} → PSet.{u} → Prop)
    (φ_resp : ∀ {x x' y y'}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
    (φ_func : ∀ {x y y'}, x ∈ s → φ x y → φ x y' → y ≈ y')
    (φ_nat : ∀ {x y}, x ∈ s → φ x y → IsNat y) :
    ∃ img : PSet.{u}, ∀ y, y ∈ img ↔ ∃ x, x ∈ s ∧ φ x y :=
  replacement (D := D) (T := NatT) (fun η => natT_coherent D s η)
    (fun e ⟨k, ep, h⟩ => ⟨k, ep, h.resp_left e⟩) φ_resp φ_func φ_nat

end PSet

open PSet in
#print axioms replacement_nat
