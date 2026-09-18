import ConCic.Worldly
/-!
First-order formulas of set theory (de Bruijn indices), satisfaction over a set structure
`(M, ∈)`, and an injective coding of formulas as sets, used to put a formula into a label.
-/
universe u

namespace PSet

inductive Fml : Type
  | mem (i j : Nat)
  | eq (i j : Nat)
  | neg (φ : Fml)
  | and (φ ψ : Fml)
  | all (φ : Fml)

def Env.cons (x : PSet.{u}) (e : Nat → PSet.{u}) : Nat → PSet.{u}
  | 0 => x
  | n+1 => e n

/-- Satisfaction in `(M, ∈)`; quantifiers range over the elements of `M`. -/
def Sat (M : PSet.{u}) : Fml → (Nat → PSet.{u}) → Prop
  | .mem i j, e => e i ∈ e j
  | .eq i j, e => e i ≈ e j
  | .neg φ, e => ¬ Sat M φ e
  | .and φ ψ, e => Sat M φ e ∧ Sat M ψ e
  | .all φ, e => ∀ x, x ∈ M → Sat M φ (Env.cons x e)

theorem Sat.resp {M M' : PSet.{u}} (eM : M ≈ M') :
    ∀ (φ : Fml) {e e' : Nat → PSet.{u}}, (∀ i, e i ≈ e' i) → Sat M φ e → Sat M' φ e'
  | .mem i j, _, _, h, s => (mem_congr_left (h i)).1 ((mem_congr_right (h j)).1 s)
  | .eq i j, _, _, h, s => (h i).symm.trans (s.trans (h j))
  | .neg φ, _, _, h, s => fun s' => s (Sat.resp eM.symm φ (fun i => (h i).symm) s')
  | .and φ ψ, _, _, h, s => ⟨Sat.resp eM φ h s.1, Sat.resp eM ψ h s.2⟩
  | .all φ, e, e', h, s => fun x hx =>
    Sat.resp eM φ (e := Env.cons x e) (fun i => by cases i <;> first | exact Equiv.refl _ | exact h _)
      (s x ((mem_congr_right eM).2 hx))

theorem ofNat_inj : ∀ {m n : Nat}, ofNat.{u} m ≈ ofNat n → m = n
  | 0, 0, _ => rfl
  | 0, _+1, h => (not_mem_empty _ ((mem_congr_right h).2 (mem_succ.2 (.inr (Equiv.refl _))))).elim
  | _+1, 0, h => (not_mem_empty _ ((mem_congr_right h).1 (mem_succ.2 (.inr (Equiv.refl _))))).elim
  | _+1, _+1, h => congrArg (· + 1) (ofNat_inj (succ_inj h))

/-- Codes: a tag followed by the components. -/
def enc : Fml → PSet.{u}
  | .mem i j => pair (ofNat 0) (pair (ofNat i) (ofNat j))
  | .eq i j => pair (ofNat 1) (pair (ofNat i) (ofNat j))
  | .neg φ => pair (ofNat 2) (enc φ)
  | .and φ ψ => pair (ofNat 3) (pair (enc φ) (enc ψ))
  | .all φ => pair (ofNat 4) (enc φ)

theorem enc_inj : ∀ {φ ψ : Fml}, enc.{u} φ ≈ enc ψ → φ = ψ := by
  intro φ
  induction φ with
  | mem i j => intro ψ h; cases ψ <;> (have ⟨t, r⟩ := pair_inj h; cases ofNat_inj t) <;>
      (have ⟨a, b⟩ := pair_inj r; cases ofNat_inj a; cases ofNat_inj b; rfl)
  | eq i j => intro ψ h; cases ψ <;> (have ⟨t, r⟩ := pair_inj h; cases ofNat_inj t) <;>
      (have ⟨a, b⟩ := pair_inj r; cases ofNat_inj a; cases ofNat_inj b; rfl)
  | neg φ ih => intro ψ h; cases ψ <;> (have ⟨t, r⟩ := pair_inj h; cases ofNat_inj t) <;>
      (cases ih r; rfl)
  | and φ₁ φ₂ ih₁ ih₂ => intro ψ h; cases ψ <;> (have ⟨t, r⟩ := pair_inj h; cases ofNat_inj t) <;>
      (have ⟨a, b⟩ := pair_inj r; cases ih₁ a; cases ih₂ b; rfl)
  | all φ ih => intro ψ h; cases ψ <;> (have ⟨t, r⟩ := pair_inj h; cases ofNat_inj t) <;>
      (cases ih r; rfl)
