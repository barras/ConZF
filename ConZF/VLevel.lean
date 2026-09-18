import ConZF.Ord
import ConZF.Pair
/-!
Power set, the levels `V_x` (for any set `x`, of rank `rank x`), finite ordinals and `ω`, and the
label set `D G = V_{G+ω}` of the definability rule, all characterized through ranks.
-/
universe u

namespace PSet

/-- Power set: subsets are indexed by predicates on the index type, which is small because
`Prop` is impredicative. -/
def powerset (X : PSet.{u}) : PSet.{u} :=
  range (ι := X.Idx → Prop) fun S => range (ι := {i // S i}) fun i => X.Func i.1

theorem mem_powerset {X y : PSet.{u}} : y ∈ powerset X ↔ ∀ z, z ∈ y → z ∈ X := by
  refine ⟨fun ⟨S, e⟩ z hz => ?_, fun h => ⟨fun i => X.Func i ∈ y, ext fun z => ⟨fun hz => ?_, ?_⟩⟩⟩
  · have ⟨⟨i, _⟩, e'⟩ := (mem_congr_right e).1 hz
    exact ⟨i, e'⟩
  · have ⟨i, e'⟩ := h z hz
    exact ⟨⟨i, (mem_congr_left e').1 hz⟩, e'⟩
  · rintro ⟨⟨i, hi⟩, e'⟩
    exact (mem_congr_left e').2 hi

/-- `z ∈ rank x` iff `z ≤ rank y` for some `y ∈ x`. -/
theorem mem_rank' {x z : PSet.{u}} : z ∈ rank x ↔ ∃ y, y ∈ x ∧ z ∈ succ (rank y) :=
  mem_rank.trans ⟨fun ⟨a, h⟩ => ⟨_, func_mem x a, h⟩,
    fun ⟨_, ⟨a, e⟩, h⟩ => ⟨a, (mem_succ_congr (rank_congr e)).1 h⟩⟩

theorem succ_congr {a a' : PSet.{u}} (h : a ≈ a') : succ a ≈ succ a' :=
  ext fun _ => mem_succ_congr h

/-- The rank of an ordinal is itself. -/
theorem IsOrd.rank_equiv : ∀ {t : PSet.{u}}, IsOrd t → rank t ≈ t := by
  intro t
  induction t using mem_induction with | _ t ih => ?_
  intro ht
  refine ext fun z => mem_rank'.trans ⟨fun ⟨y, hy, hz⟩ => ?_, fun hz => ⟨z, hz, ?_⟩⟩
  · rcases mem_succ.1 ((mem_succ_congr (ih y hy (ht.mem hy))).1 hz) with hz | e
    · exact ht.trans y hy z hz
    · exact (mem_congr_left e).2 hy
  · exact (mem_succ_congr (ih z hz (ht.mem hz))).2 (mem_succ.2 (.inr (Equiv.refl _)))

section em
variable (em : ∀ p : Prop, p ∨ ¬p)
include em

/-- If every element of `y` has rank below the ordinal `R`, then `rank y ≤ R`. -/
theorem rank_mem_succ {y R : PSet.{u}} (hR : IsOrd R) (h : ∀ z, z ∈ y → rank z ∈ R) :
    rank y ∈ succ R := by
  refine mem_succ.2 ((isOrd_rank y).subset em hR fun w hw => ?_)
  have ⟨z, hz, hw⟩ := mem_rank'.1 hw
  rcases mem_succ.1 hw with hw | e
  · exact hR.trans _ (h z hz) w hw
  · exact (mem_congr_left e).2 (h z hz)

theorem rank_singleton_mem {a R : PSet.{u}} (hR : IsOrd R) (ha : rank a ∈ R) :
    rank (singleton a) ∈ succ R :=
  rank_mem_succ em hR fun _ hz => (mem_congr_left (rank_congr (mem_singleton.1 hz))).2 ha

theorem rank_upair_mem {a b R : PSet.{u}} (hR : IsOrd R) (ha : rank a ∈ R) (hb : rank b ∈ R) :
    rank (upair a b) ∈ succ R :=
  rank_mem_succ em hR fun _ hz => (mem_upair.1 hz).elim
    (fun e => (mem_congr_left (rank_congr e)).2 ha) (fun e => (mem_congr_left (rank_congr e)).2 hb)

theorem rank_pair_mem {a b R : PSet.{u}} (hR : IsOrd R) (ha : rank a ∈ R) (hb : rank b ∈ R) :
    rank (pair a b) ∈ succ (succ R) :=
  rank_upair_mem em hR.succ (rank_singleton_mem em hR ha) (rank_upair_mem em hR ha hb)

theorem rank_triple_mem {a b c R : PSet.{u}} (hR : IsOrd R)
    (ha : rank a ∈ R) (hb : rank b ∈ R) (hc : rank c ∈ R) :
    rank (triple a b c) ∈ succ (succ (succ (succ R))) :=
  rank_pair_mem em hR.succ.succ
    (mem_succ.2 (.inl (mem_succ.2 (.inl ha)))) (rank_pair_mem em hR hb hc)

end em

/-! ### Levels -/

/-- `Vl x` is the set of sets of rank below `rank x`. -/
def Vl : PSet.{u} → PSet.{u}
  | ⟨_, A⟩ => iUnion fun a => powerset (Vl (A a))

theorem mem_Vl (em : ∀ p : Prop, p ∨ ¬p) : ∀ {x y : PSet.{u}}, y ∈ Vl x ↔ rank y ∈ rank x
  | ⟨_, A⟩, y => by
    refine mem_iUnion.trans <| .trans ?_ mem_rank.symm
    refine exists_congr fun a => mem_powerset.trans ⟨fun h => ?_, fun h z hz => ?_⟩
    · exact rank_mem_succ em (isOrd_rank _) fun z hz => (mem_Vl em).1 (h z hz)
    · refine (mem_Vl em).2 ?_
      have hz' := rank_mem hz
      rcases mem_succ.1 h with h | e
      · exact (isOrd_rank _).trans _ h _ hz'
      · exact (mem_congr_right e).1 hz'

/-! ### Finite ordinals and `ω` -/

def ofNat : Nat → PSet.{u}
  | 0 => empty
  | n+1 => succ (ofNat n)

theorem isOrd_ofNat : ∀ n, IsOrd (ofNat.{u} n)
  | 0 => isOrd_empty
  | n+1 => (isOrd_ofNat n).succ

def omega : PSet.{u} := range (ι := ULift.{u} Nat) fun n => ofNat n.down

theorem mem_omega {x : PSet.{u}} : x ∈ omega ↔ ∃ n, x ≈ ofNat n :=
  ⟨fun ⟨n, e⟩ => ⟨n.down, e⟩, fun ⟨n, e⟩ => ⟨⟨n⟩, e⟩⟩

theorem isOrd_omega : IsOrd omega.{u} := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · have ⟨n, e⟩ := mem_omega.1 hy
    induction n generalizing y z with
    | zero => exact ((not_mem_empty z) ((mem_congr_right e).1 hz)).elim
    | succ n ih =>
      rcases mem_succ.1 ((mem_congr_right e).1 hz) with h | e'
      · exact ih _ (mem_omega.2 ⟨n, Equiv.refl _⟩) _ h (Equiv.refl _)
      · exact mem_omega.2 ⟨n, e'⟩
  · have ⟨n, e⟩ := mem_omega.1 hy
    exact ((isOrd_ofNat n).resp e.symm).trans

/-! ### The label set -/

def succN : Nat → PSet.{u} → PSet.{u}
  | 0, G => G
  | n+1, G => succ (succN n G)

/-- `D G = V_{rank G + ω}`. -/
def D (G : PSet.{u}) : PSet.{u} := iUnion (ι := ULift.{u} Nat) fun n => Vl (succN n.down G)

theorem mem_D (em : ∀ p : Prop, p ∨ ¬p) {G y : PSet.{u}} :
    y ∈ D G ↔ ∃ n, rank y ∈ rank (succN n G) :=
  mem_iUnion.trans ⟨fun ⟨n, h⟩ => ⟨n.down, (mem_Vl em).1 h⟩, fun ⟨n, h⟩ => ⟨⟨n⟩, (mem_Vl em).2 h⟩⟩

theorem IsOrd.iterate_succ {G : PSet.{u}} (h : IsOrd G) : ∀ n, IsOrd (succN n G)
  | 0 => h
  | n+1 => (h.iterate_succ n).succ

/-- For an ordinal `G`, a set whose rank is below `G + n` is in `D G`. -/
theorem mem_D_of_rank (em : ∀ p : Prop, p ∨ ¬p) {G y : PSet.{u}} (hG : IsOrd G) (n : Nat)
    (h : rank y ∈ succN n G) : y ∈ D G :=
  (mem_D em).2 ⟨n, (mem_congr_right (hG.iterate_succ n).rank_equiv).2 h⟩
