import ConCic.NatInstance
/-!
Ordinals and rank. Excluded middle, where needed, is an explicit hypothesis
`em : ∀ p : Prop, p ∨ ¬p`, never `Classical.em` (which is proved from choice).
-/
universe u

namespace PSet

def Trans (t : PSet.{u}) : Prop := ∀ y, y ∈ t → ∀ z, z ∈ y → z ∈ t

/-- Von Neumann ordinals: transitive sets of transitive sets (foundation is built in). -/
structure IsOrd (t : PSet.{u}) : Prop where
  trans : Trans t
  mem_trans : ∀ y, y ∈ t → Trans y

theorem Trans.resp {t t' : PSet.{u}} (e : t ≈ t') (h : Trans t) : Trans t' :=
  fun y hy z hz => (mem_congr_right e).1 (h y ((mem_congr_right e).2 hy) z hz)

theorem IsOrd.resp {t t' : PSet.{u}} (e : t ≈ t') (h : IsOrd t) : IsOrd t' :=
  ⟨h.trans.resp e, fun y hy => h.mem_trans y ((mem_congr_right e).2 hy)⟩

theorem IsOrd.mem {t y : PSet.{u}} (h : IsOrd t) (hy : y ∈ t) : IsOrd y :=
  ⟨h.mem_trans y hy, fun z hz => h.mem_trans z (h.trans y hy z hz)⟩

theorem isOrd_empty : IsOrd empty.{u} :=
  ⟨fun _ h => (not_mem_empty _ h).elim, fun _ h => (not_mem_empty _ h).elim⟩

theorem IsOrd.succ {t : PSet.{u}} (h : IsOrd t) : IsOrd (succ t) := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · rcases mem_succ.1 hy with hy | e
    · exact mem_succ.2 (.inl (h.trans y hy z hz))
    · exact mem_succ.2 (.inl ((mem_congr_right e).1 hz))
  · rcases mem_succ.1 hy with hy | e
    · exact h.mem_trans y hy
    · exact h.trans.resp e.symm

theorem isOrd_iUnion {ι : Type u} {A : ι → PSet.{u}} (h : ∀ i, IsOrd (A i)) : IsOrd (iUnion A) := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · have ⟨i, hi⟩ := mem_iUnion.1 hy
    exact mem_iUnion.2 ⟨i, (h i).trans y hi z hz⟩
  · have ⟨i, hi⟩ := mem_iUnion.1 hy
    exact (h i).mem_trans y hi

theorem not_mem_self (a : PSet.{u}) : ¬ a ∈ a := fun h => mem_asymm a h h

section em
variable (em : ∀ p : Prop, p ∨ ¬p)
include em

/-- Ordinals are linearly ordered by `∈`. -/
theorem IsOrd.trichotomy : ∀ {a b : PSet.{u}}, IsOrd a → IsOrd b → a ∈ b ∨ a ≈ b ∨ b ∈ a := by
  intro a
  induction a using mem_induction with | _ a iha => ?_
  intro b
  induction b using mem_induction with | _ b ihb => ?_
  intro ha hb
  rcases em (a ∈ b) with h1 | h1
  · exact .inl h1
  rcases em (b ∈ a) with h2 | h2
  · exact .inr (.inr h2)
  refine .inr (.inl (ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩))
  · rcases iha z hz (ha.mem hz) hb with h | h | h
    · exact h
    · exact (h2 ((mem_congr_left h).1 hz)).elim
    · exact (h2 (ha.trans z hz b h)).elim
  · rcases ihb z hz ha (hb.mem hz) with h | h | h
    · exact (h1 (hb.trans z hz a h)).elim
    · exact (h1 ((mem_congr_left h).2 hz)).elim
    · exact h

/-- For ordinals, inclusion is `∈` or `≈`. -/
theorem IsOrd.subset {a b : PSet.{u}} (ha : IsOrd a) (hb : IsOrd b) (h : ∀ z, z ∈ a → z ∈ b) :
    a ∈ b ∨ a ≈ b := by
  rcases ha.trichotomy em hb with h' | h' | h'
  · exact .inl h'
  · exact .inr h'
  · exact (not_mem_self b (h b h')).elim

end em

/-! ### Rank -/

def rank : PSet.{u} → PSet.{u}
  | ⟨_, A⟩ => iUnion fun a => succ (rank (A a))

theorem mem_rank {x z : PSet.{u}} : z ∈ rank x ↔ ∃ a, z ∈ succ (rank (x.Func a)) := by
  cases x; exact mem_iUnion

theorem rank_congr : ∀ {x y : PSet.{u}}, x ≈ y → rank x ≈ rank y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨h1, h2⟩ => ext fun _ =>
    ⟨fun h => have ⟨a, h⟩ := mem_iUnion.1 h
       have ⟨b, e⟩ := h1 a
       mem_iUnion.2 ⟨b, (mem_succ_congr (rank_congr e)).1 h⟩,
     fun h => have ⟨b, h⟩ := mem_iUnion.1 h
       have ⟨a, e⟩ := h2 b
       mem_iUnion.2 ⟨a, (mem_succ_congr (rank_congr e)).2 h⟩⟩

theorem rank_mem {x y : PSet.{u}} (h : y ∈ x) : rank y ∈ rank x :=
  have ⟨a, e⟩ := h
  mem_rank.2 ⟨a, mem_succ.2 (.inr (rank_congr e))⟩

theorem isOrd_rank : ∀ x : PSet.{u}, IsOrd (rank x)
  | ⟨_, A⟩ => isOrd_iUnion fun a => (isOrd_rank (A a)).succ
