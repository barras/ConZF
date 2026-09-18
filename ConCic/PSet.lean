/-
Sets as trees (Aczel), from scratch in Lean core, so that `#print axioms` shows exactly what
is used. Nothing here uses `Classical.choice`.
-/
universe u

/-- `V = W X : Type u. X`. -/
inductive PSet : Type (u+1)
  | mk (α : Type u) (A : α → PSet) : PSet

namespace PSet

def Idx : PSet.{u} → Type u | ⟨α, _⟩ => α
def Func : (x : PSet.{u}) → x.Idx → PSet.{u} | ⟨_, A⟩ => A

theorem mk_eta : (x : PSet.{u}) → x = ⟨x.Idx, x.Func⟩ | ⟨_, _⟩ => rfl

/-- Bisimulation. -/
def Equiv : PSet.{u} → PSet.{u} → Prop
  | ⟨_, A⟩, ⟨_, B⟩ => (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b))

infixl:50 " ≈ " => Equiv

theorem Equiv.refl : (x : PSet.{u}) → x ≈ x
  | ⟨_, A⟩ => ⟨fun a => ⟨a, Equiv.refl (A a)⟩, fun a => ⟨a, Equiv.refl (A a)⟩⟩

theorem Equiv.symm : {x y : PSet.{u}} → x ≈ y → y ≈ x
  | ⟨_, _⟩, ⟨_, _⟩, ⟨h1, h2⟩ =>
    ⟨fun b => let ⟨a, h⟩ := h2 b; ⟨a, h.symm⟩, fun a => let ⟨b, h⟩ := h1 a; ⟨b, h.symm⟩⟩

theorem Equiv.trans : {x y z : PSet.{u}} → x ≈ y → y ≈ z → x ≈ z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨h1, h2⟩, ⟨k1, k2⟩ =>
    ⟨fun a => let ⟨b, h⟩ := h1 a; let ⟨c, k⟩ := k1 b; ⟨c, h.trans k⟩,
     fun c => let ⟨b, k⟩ := k2 c; let ⟨a, h⟩ := h2 b; ⟨a, h.trans k⟩⟩

def Mem (x y : PSet.{u}) : Prop := ∃ b, x ≈ y.Func b

instance : Membership PSet.{u} PSet.{u} := ⟨fun y x => Mem x y⟩

theorem mem_def {x y : PSet.{u}} : x ∈ y ↔ ∃ b, x ≈ y.Func b := Iff.rfl

theorem func_mem (y : PSet.{u}) (b : y.Idx) : y.Func b ∈ y := ⟨b, Equiv.refl _⟩

theorem mem_congr_left {x x' y : PSet.{u}} (h : x ≈ x') : x ∈ y ↔ x' ∈ y :=
  ⟨fun ⟨b, e⟩ => ⟨b, h.symm.trans e⟩, fun ⟨b, e⟩ => ⟨b, h.trans e⟩⟩

theorem equiv_iff_mem : {x y : PSet.{u}} → (x ≈ y ↔ ∀ z, z ∈ x ↔ z ∈ y)
  | ⟨_, A⟩, ⟨_, B⟩ =>
    ⟨fun ⟨h1, h2⟩ _ =>
      ⟨fun ⟨a, e⟩ => let ⟨b, h⟩ := h1 a; ⟨b, e.trans h⟩,
       fun ⟨b, e⟩ => let ⟨a, h⟩ := h2 b; ⟨a, e.trans h.symm⟩⟩,
     fun H =>
      ⟨fun a => (H (A a)).1 ⟨a, Equiv.refl _⟩,
       fun b => let ⟨a, e⟩ := (H (B b)).2 ⟨b, Equiv.refl _⟩; ⟨a, e.symm⟩⟩⟩

theorem ext {x y : PSet.{u}} (H : ∀ z, z ∈ x ↔ z ∈ y) : x ≈ y := equiv_iff_mem.2 H

theorem mem_congr_right {x y y' : PSet.{u}} (h : y ≈ y') : x ∈ y ↔ x ∈ y' :=
  equiv_iff_mem.1 h x

/-- `∈`-induction, for predicates that need not respect `≈`. -/
theorem mem_induction {P : PSet.{u} → Prop} (H : ∀ x, (∀ y, y ∈ x → P y) → P x) (x : PSet.{u}) :
    P x := by
  suffices ∀ x y, y ≈ x → P y from this x x (Equiv.refl x)
  intro x
  induction x with
  | mk α A ih =>
    intro y hy
    refine H y fun z hz => ?_
    have ⟨a, e⟩ := (mem_congr_right hy).1 hz
    exact ih a z e

/-! ### Operations -/

def empty : PSet.{u} := ⟨PEmpty, PEmpty.elim⟩

theorem not_mem_empty (x : PSet.{u}) : ¬ x ∈ empty := fun ⟨b, _⟩ => b.elim

/-- The set `{A i | i : ι}` of a family indexed by a small type. -/
def range {ι : Type u} (A : ι → PSet.{u}) : PSet.{u} := ⟨ι, A⟩

theorem mem_range {ι : Type u} {A : ι → PSet.{u}} {x} : x ∈ range A ↔ ∃ i, x ≈ A i := Iff.rfl

def sUnion (a : PSet.{u}) : PSet.{u} :=
  ⟨Σ x : a.Idx, (a.Func x).Idx, fun p => (a.Func p.1).Func p.2⟩

theorem mem_sUnion {a x : PSet.{u}} : x ∈ sUnion a ↔ ∃ y, y ∈ a ∧ x ∈ y := by
  constructor
  · rintro ⟨⟨i, j⟩, e⟩
    exact ⟨a.Func i, func_mem _ _, j, e⟩
  · rintro ⟨y, ⟨i, e⟩, hx⟩
    have ⟨j, e'⟩ := (mem_congr_right e).1 hx
    exact ⟨⟨i, j⟩, e'⟩

/-- `⋃ i, A i` for a family indexed by a small type. -/
def iUnion {ι : Type u} (A : ι → PSet.{u}) : PSet.{u} := sUnion (range A)

theorem mem_iUnion {ι : Type u} {A : ι → PSet.{u}} {x} : x ∈ iUnion A ↔ ∃ i, x ∈ A i := by
  rw [iUnion, mem_sUnion]
  constructor
  · rintro ⟨y, ⟨i, e⟩, hx⟩
    exact ⟨i, (mem_congr_right e).1 hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨A i, ⟨i, Equiv.refl _⟩, hx⟩

/-- The union of a family indexed by the proofs of a proposition: `t` if `P` holds, `∅` if not.
This is what replaces a decision procedure for `P`. -/
def guard (P : Prop) (t : P → PSet.{u}) : PSet.{u} :=
  iUnion (ι := ULift.{u} (PLift P)) fun h => t h.down.down

theorem mem_guard {P : Prop} {t : P → PSet.{u}} {x} : x ∈ guard P t ↔ ∃ h : P, x ∈ t h := by
  rw [guard, mem_iUnion]
  exact ⟨fun ⟨h, hx⟩ => ⟨h.down.down, hx⟩, fun ⟨h, hx⟩ => ⟨⟨⟨h⟩⟩, hx⟩⟩

def union (a b : PSet.{u}) : PSet.{u} :=
  iUnion (ι := ULift.{u} Bool) fun i => if i.down then a else b

theorem mem_union {a b x : PSet.{u}} : x ∈ union a b ↔ x ∈ a ∨ x ∈ b := by
  rw [union, mem_iUnion]
  constructor
  · rintro ⟨⟨_ | _⟩, h⟩
    · exact .inr h
    · exact .inl h
  · rintro (h | h)
    · exact ⟨⟨true⟩, h⟩
    · exact ⟨⟨false⟩, h⟩

def singleton (a : PSet.{u}) : PSet.{u} := range (ι := PUnit) fun _ => a

theorem mem_singleton {a x : PSet.{u}} : x ∈ singleton a ↔ x ≈ a :=
  ⟨fun ⟨_, e⟩ => e, fun e => ⟨⟨⟩, e⟩⟩

def succ (a : PSet.{u}) : PSet.{u} := union a (singleton a)

theorem mem_succ {a x : PSet.{u}} : x ∈ succ a ↔ x ∈ a ∨ x ≈ a := by
  rw [succ, mem_union, mem_singleton]

theorem mem_succ_congr {a a' x : PSet.{u}} (h : a ≈ a') : x ∈ succ a ↔ x ∈ succ a' := by
  rw [mem_succ, mem_succ, mem_congr_right h]
  exact or_congr Iff.rfl ⟨fun e => e.trans h, fun e => e.trans h.symm⟩

/-- Separation. -/
def sep (p : PSet.{u} → Prop) (a : PSet.{u}) : PSet.{u} :=
  range (ι := {i : a.Idx // p (a.Func i)}) fun i => a.Func i.1

theorem mem_sep {p : PSet.{u} → Prop} (hp : ∀ x y, x ≈ y → p x → p y) {a x : PSet.{u}} :
    x ∈ sep p a ↔ x ∈ a ∧ p x :=
  ⟨fun ⟨⟨i, h⟩, e⟩ => ⟨⟨i, e⟩, hp _ _ e.symm h⟩,
   fun ⟨⟨i, e⟩, h⟩ => ⟨⟨i, hp _ _ e h⟩, e⟩⟩

end PSet
