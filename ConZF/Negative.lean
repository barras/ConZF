import ConZF.PSet
/-!
The negative (Gödel–Gentzen) reading of the sets-as-trees, as a probe for eliminating excluded
middle: bisimulation and membership with `¬¬∃` in place of `∃` at every level. They are stable,
extensionality holds, and `∈ⁿ`-induction holds **for stable predicates**. It does not hold for
arbitrary predicates, in particular not for accessibility, which is where the elimination of
excluded middle from `con_ZF` gets stuck (see `doc/main.tex`, Discussion).
-/
universe u

namespace PSet

/-- Bisimulation in the negative translation. -/
def NEquiv : PSet.{u} → PSet.{u} → Prop
  | ⟨_, A⟩, ⟨_, B⟩ => (∀ a, ¬¬∃ b, NEquiv (A a) (B b)) ∧ (∀ b, ¬¬∃ a, NEquiv (A a) (B b))

infixl:50 " ≈ⁿ " => NEquiv

def NMem (x y : PSet.{u}) : Prop := ¬¬∃ b, x ≈ⁿ y.Func b

infixl:50 " ∈ⁿ " => NMem

theorem NEquiv.stable : ∀ {x y : PSet.{u}}, ¬¬x ≈ⁿ y → x ≈ⁿ y
  | ⟨_, _⟩, ⟨_, _⟩, h =>
    ⟨fun a hn => h fun e => e.1 a hn, fun b hn => h fun e => e.2 b hn⟩

theorem NMem.stable {x y : PSet.{u}} (h : ¬¬x ∈ⁿ y) : x ∈ⁿ y := fun hn => h fun h' => h' hn

theorem NEquiv.refl : (x : PSet.{u}) → x ≈ⁿ x
  | ⟨_, A⟩ => ⟨fun a hn => hn ⟨a, NEquiv.refl (A a)⟩, fun a hn => hn ⟨a, NEquiv.refl (A a)⟩⟩

theorem NEquiv.symm : {x y : PSet.{u}} → x ≈ⁿ y → y ≈ⁿ x
  | ⟨_, _⟩, ⟨_, _⟩, ⟨h1, h2⟩ =>
    ⟨fun b hn => h2 b fun ⟨a, h⟩ => hn ⟨a, h.symm⟩, fun a hn => h1 a fun ⟨b, h⟩ => hn ⟨b, h.symm⟩⟩

theorem NEquiv.trans : {x y z : PSet.{u}} → x ≈ⁿ y → y ≈ⁿ z → x ≈ⁿ z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨h1, h2⟩, ⟨k1, k2⟩ =>
    ⟨fun a hn => h1 a fun ⟨b, h⟩ => k1 b fun ⟨c, k⟩ => hn ⟨c, h.trans k⟩,
     fun c hn => k2 c fun ⟨b, k⟩ => h2 b fun ⟨a, h⟩ => hn ⟨a, h.trans k⟩⟩

theorem nmem_congr_left {x x' y : PSet.{u}} (e : x ≈ⁿ x') (h : x ∈ⁿ y) : x' ∈ⁿ y :=
  fun hn => h fun ⟨b, hb⟩ => hn ⟨b, e.symm.trans hb⟩

theorem func_nmem (y : PSet.{u}) (b : y.Idx) : y.Func b ∈ⁿ y := fun hn => hn ⟨b, NEquiv.refl _⟩

/-- Extensionality in the negative reading. -/
theorem NEquiv.ext : {x y : PSet.{u}} → (∀ z, z ∈ⁿ x → z ∈ⁿ y) → (∀ z, z ∈ⁿ y → z ∈ⁿ x) → x ≈ⁿ y
  | ⟨_, A⟩, ⟨_, B⟩, h1, h2 =>
    ⟨fun a => h1 (A a) (func_nmem ⟨_, A⟩ a),
     fun b hn => h2 (B b) (func_nmem ⟨_, B⟩ b) fun ⟨a, e⟩ => hn ⟨a, e.symm⟩⟩

theorem nmem_congr_right : {x y y' : PSet.{u}} → y ≈ⁿ y' → x ∈ⁿ y → x ∈ⁿ y'
  | _, ⟨_, _⟩, ⟨_, _⟩, ⟨h1, _⟩, h => fun hn =>
    h fun ⟨a, ea⟩ => h1 a fun ⟨b, eb⟩ => hn ⟨b, ea.trans eb⟩

/-- `∈ⁿ`-induction, for **stable** predicates. The stability of `P` is used to pass from
`¬¬∃ a, z ≈ⁿ A a` to `P z`; for a predicate such as accessibility this step is an instance of
the double negation shift. -/
theorem nmem_induction {P : PSet.{u} → Prop} (stable : ∀ x, ¬¬P x → P x)
    (H : ∀ x, (∀ y, y ∈ⁿ x → P y) → P x) (x : PSet.{u}) : P x := by
  suffices ∀ x y, y ≈ⁿ x → P y from this x x (NEquiv.refl x)
  intro x
  induction x with
  | mk α A ih =>
    intro y hy
    refine H y fun z hz => stable z fun hn => ?_
    exact nmem_congr_right hy hz fun ⟨a, e⟩ => hn (ih a z e)
