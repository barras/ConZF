import ConCic.Rule
import ConCic.VLevel
/-!
The definability rule (paper3, Lemma `worldlyrule`, Theorem `bigacc`).

`I η q x y` is an arbitrary notion of "`y` is the value at `x` of the function defined over
`V_η` with parameter `q`". For the theorem in the paper it is satisfaction of a formula over
`V_η`, with `q` a pair of a formula code and a parameter; nothing here depends on that.
A limit `η > ω` is *reachable* if some `I`-definable function with parameters of rank below some
`ν ∈ η` has values of rank unbounded in `η`. The rule gives every ordinal that is `0`, a successor,
`ω` or reachable a coherent assignment. So either every ordinal has one, and then Replacement
holds, or some ordinal is none of these, which is a limit above `ω` into which no definable
function from a smaller set is cofinal (for first-order `I`: a worldly cardinal).
-/
universe u

namespace PSet

variable (I : PSet.{u} → PSet.{u} → PSet.{u} → PSet.{u} → Prop)

/-- `(q, s)` defines, over `V_η`, a partial function on `s` with values of rank unbounded in `η`. -/
def Unb (η q s : PSet.{u}) : Prop :=
  (∀ x y y', x ∈ s → I η q x y → I η q x y' → y ≈ y') ∧
  (∀ x y, x ∈ s → I η q x y → rank y ∈ η) ∧
  (∀ ζ, ζ ∈ η → ∃ x y, x ∈ s ∧ I η q x y ∧ ζ ∈ succ (rank y))

/-- `η` is reached from parameters of rank below `ν`. -/
def Reach (η ν : PSet.{u}) : Prop := ∃ q s, rank q ∈ ν ∧ rank s ∈ ν ∧ Unb I η q s

def IsSucc (η : PSet.{u}) : Prop := ∃ ζ, η ≈ succ ζ

/-- The case of the rule that uses definable functions. -/
def LimCase (η : PSet.{u}) : Prop := ¬ IsSucc η ∧ ¬ η ≈ omega ∧ ∃ ν, ν ∈ η ∧ Reach I η ν

/-- The least `ν` from which `η` is reached, as the set of the `ν ∈ η` from which it is not. -/
def Gν (η : PSet.{u}) : PSet.{u} := sep (fun ν => ¬ Reach I η ν) η

/-- The target of the child `a`. -/
def RuleA (η ξ : PSet.{u}) : Prop :=
  η ≈ succ ξ ∨ (η ≈ omega ∧ ξ ≈ empty) ∨ (LimCase I η ∧ ξ ≈ Gν I η)

/-- The target of the child `b w`. -/
def RuleB (η w ξ : PSet.{u}) : Prop :=
  (η ≈ omega ∧ rank w ∈ omega ∧ ξ ≈ rank w) ∨
  (LimCase I η ∧ ∃ q s x y, w ≈ triple q s x ∧ Unb I η q s ∧ x ∈ s ∧ I η q x y ∧ ξ ≈ rank y)

def rule (η : PSet.{u}) : Label.{u} → PSet.{u} → Prop
  | .a => RuleA I η
  | .b w => RuleB I η w
  | .c _ => fun _ => False

theorem omega_not_succ {ζ : PSet.{u}} (h : omega ≈ succ ζ) : False := by
  have ⟨n, e⟩ := mem_omega.1 ((mem_congr_right h).2 (mem_succ.2 (.inr (Equiv.refl ζ))))
  have h1 : succ ζ ∈ omega := mem_omega.2 ⟨n+1, succ_congr e⟩
  exact not_mem_self _ ((mem_congr_right h).1 h1)

/-! ### Invariance -/

variable {I}
variable (I_resp : ∀ {η η' q q' x x' y y' : PSet.{u}},
  η ≈ η' → q ≈ q' → x ≈ x' → y ≈ y' → I η q x y → I η' q' x' y')
include I_resp

theorem Unb.resp {η η' q q' s s' : PSet.{u}} (eη : η ≈ η') (eq : q ≈ q') (es : s ≈ s')
    (h : Unb I η q s) : Unb I η' q' s' := by
  have back : ∀ {x y}, I η' q' x y → I η q x y :=
    I_resp eη.symm eq.symm (Equiv.refl _) (Equiv.refl _)
  refine ⟨fun x y y' hx h1 h2 => h.1 x y y' ((mem_congr_right es).2 hx) (back h1) (back h2),
    fun x y hx h1 => (mem_congr_right eη).1 (h.2.1 x y ((mem_congr_right es).2 hx) (back h1)),
    fun ζ hζ => ?_⟩
  have ⟨x, y, hx, h1, h2⟩ := h.2.2 ζ ((mem_congr_right eη).2 hζ)
  exact ⟨x, y, (mem_congr_right es).1 hx,
    I_resp eη eq (Equiv.refl _) (Equiv.refl _) h1, h2⟩

theorem Reach.resp {η η' ν ν' : PSet.{u}} (eη : η ≈ η') (eν : ν ≈ ν') (h : Reach I η ν) :
    Reach I η' ν' :=
  have ⟨q, s, hq, hs, h⟩ := h
  ⟨q, s, (mem_congr_right eν).1 hq, (mem_congr_right eν).1 hs,
    h.resp I_resp eη (Equiv.refl _) (Equiv.refl _)⟩

omit I_resp in
theorem IsSucc.resp {η η' : PSet.{u}} (e : η ≈ η') (h : IsSucc η) : IsSucc η' :=
  have ⟨ζ, h⟩ := h; ⟨ζ, e.symm.trans h⟩

theorem LimCase.resp {η η' : PSet.{u}} (e : η ≈ η') (h : LimCase I η) : LimCase I η' :=
  have ⟨h1, h2, ν, hν, h3⟩ := h
  ⟨fun h => h1 (h.resp e.symm), fun h => h2 (e.trans h),
    ν, (mem_congr_right e).1 hν, h3.resp I_resp e (Equiv.refl _)⟩

theorem mem_Gν {η z : PSet.{u}} : z ∈ Gν I η ↔ z ∈ η ∧ ¬ Reach I η z :=
  mem_sep fun _ _ e h h' => h (h'.resp I_resp (Equiv.refl _) e.symm)

theorem Gν_resp {η η' : PSet.{u}} (e : η ≈ η') : Gν I η ≈ Gν I η' :=
  ext fun _ => (mem_Gν I_resp).trans <| .trans
    (and_congr (mem_congr_right e) ⟨fun h h' => h (h'.resp I_resp e.symm (Equiv.refl _)),
      fun h h' => h (h'.resp I_resp e (Equiv.refl _))⟩) (mem_Gν I_resp).symm

theorem rule_resp {η η' : PSet.{u}} {l l' : Label.{u}} {ξ ξ' : PSet.{u}}
    (eη : η ≈ η') (el : l.Equiv l') (eξ : ξ ≈ ξ') (h : rule I η l ξ) : rule I η' l' ξ' := by
  cases el with
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
  | c => exact h.elim

theorem rule_func {η : PSet.{u}} {l : Label.{u}} {ξ ξ' : PSet.{u}}
    (h : rule I η l ξ) (h' : rule I η l ξ') : ξ ≈ ξ' := by
  cases l with
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
  | c => exact h.elim

/-! ### The class of the rule -/

variable (I) in
def Good (η : PSet.{u}) : Prop :=
  η ≈ empty ∨ IsSucc η ∨ η ≈ omega ∨ ∃ ν, ν ∈ η ∧ Reach I η ν

variable (I) in
/-- Ordinals all of whose predecessors, and itself, are handled by one of the cases. -/
def Cls (η : PSet.{u}) : Prop := IsOrd η ∧ ∀ μ, (μ ∈ η ∨ μ ≈ η) → Good I μ

omit I_resp in
theorem Cls.resp {η η' : PSet.{u}} (e : η ≈ η') (h : Cls I η) : Cls I η' :=
  ⟨h.1.resp e, fun μ hμ => h.2 μ (hμ.elim (fun h => .inl ((mem_congr_right e).2 h))
    (fun h => .inr (h.trans e.symm)))⟩

omit I_resp in
theorem Cls.mem {η ξ : PSet.{u}} (h : Cls I η) (hξ : ξ ∈ η) : Cls I ξ :=
  ⟨h.1.mem hξ, fun μ hμ => h.2 μ (.inl (hμ.elim (fun h' => h.1.trans ξ hξ μ h')
    (fun e => (mem_congr_left e).2 hξ)))⟩

omit I_resp in
theorem succN_congr {G G' : PSet.{u}} (e : G ≈ G') : ∀ n, succN n G ≈ succN n G'
  | 0 => e
  | n+1 => succ_congr (succN_congr e n)

omit I_resp in
theorem succN_empty {G : PSet.{u}} (e : G ≈ empty) : ∀ n, succN n G ≈ ofNat n
  | 0 => e
  | n+1 => succ_congr (succN_empty e n)

section em
variable (em : ∀ p : Prop, p ∨ ¬p)
include em

/-- In the limit case, the least `ν` is an element of `η` from which `η` is reached. -/
theorem Gν_spec {η : PSet.{u}} (hη : IsOrd η) (h : LimCase I η) :
    Gν I η ∈ η ∧ IsOrd (Gν I η) ∧ Reach I η (Gν I η) := by
  have up : ∀ {ν ν'}, ν' ∈ η → ν ∈ ν' → Reach I η ν → Reach I η ν' :=
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
  refine ⟨hmem, hG, (em _).resolve_right fun hn => not_mem_self _ ((mem_Gν I_resp).2 ⟨hmem, hn⟩)⟩

theorem rule_mem {η : PSet.{u}} {l : Label.{u}} {ξ : PSet.{u}} (hη : Cls I η)
    (h : rule I η l ξ) : ξ ∈ η ∧ Cls I ξ := by
  suffices ξ ∈ η from ⟨this, hη.mem this⟩
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
  | c => exact h.elim

theorem rule_sup (U : PSet.{u}) {η G : PSet.{u}} (hη : Cls I η)
    (hG : ∀ x, x ∈ G ↔ ∃ ζ, rule I η .a ζ ∧ x ∈ ζ) (x : PSet.{u}) :
    x ∈ η ↔ ∃ l ξ, Avail D U G l ∧ rule I η l ξ ∧ x ∈ succ ξ := by
  refine ⟨fun hx => ?_, fun ⟨l, ξ, _, hr, hx⟩ => ?_⟩
  rotate_left
  · have hξ := (rule_mem I_resp em hη hr).1
    rcases mem_succ.1 hx with hx | e
    · exact hη.1.trans ξ hξ x hx
    · exact (mem_congr_left e).2 hξ
  -- `G` is the target of the child `a`
  have hGa : ∀ {ζ}, rule I η .a ζ → G ≈ ζ := fun {ζ} hζ => ext fun z =>
    (hG z).trans ⟨fun ⟨ζ', h1, h2⟩ => (mem_congr_right (rule_func I_resp h1 hζ)).1 h2,
      fun h => ⟨ζ, hζ, h⟩⟩
  rcases em (IsSucc η) with ⟨ζ, e⟩ | hs
  · exact ⟨.a, ζ, .inl rfl, .inl e, (mem_congr_right e).1 hx⟩
  rcases em (η ≈ omega) with hω | hω
  · have ⟨n, e⟩ := mem_omega.1 ((mem_congr_right hω).1 hx)
    have hGe : G ≈ empty := hGa (.inr (.inl ⟨hω, Equiv.refl _⟩))
    have hr : rank (ofNat.{u} n) ≈ ofNat n := (isOrd_ofNat n).rank_equiv
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
    .inr ⟨hL, q, s, x', y, Equiv.refl _, hu, hx', hI, Equiv.refl _⟩, hxy⟩

/-- The definability rule meets the one-node conditions, for the class `Cls I`. -/
theorem worldly_rule (U : PSet.{u}) : Rule D U (rule I) (Cls I) :=
  ⟨rule_func I_resp, rule_resp I_resp, Cls.resp, rule_mem I_resp em,
   fun hη hG x => rule_sup I_resp em U hη hG x⟩

end em

/-! ### The dichotomy -/

omit I_resp in
variable (I) in
/-- Either Replacement holds for every functional relation (any proposition, not only a
definable one), or there is an ordinal that is not `0`, not a successor, not `ω`, and into which
no `I`-definable function from parameters of smaller rank is cofinal. For first-order `I` the
latter is a worldly cardinal, and `V_ρ ⊨ ZF`. -/
theorem dichotomy (em : ∀ p : Prop, p ∨ ¬p) (I_resp : ∀ {η η' q q' x x' y y' : PSet.{u}},
      η ≈ η' → q ≈ q' → x ≈ x' → y ≈ y' → I η q x y → I η' q' x' y') :
    (∀ (s : PSet.{u}) (φ : PSet.{u} → PSet.{u} → Prop),
      (∀ {x x' y y'}, x ≈ x' → y ≈ y' → φ x y → φ x' y') →
      (∀ {x y y'}, x ∈ s → φ x y → φ x y' → y ≈ y') →
      ∃ img : PSet.{u}, ∀ y, y ∈ img ↔ ∃ x, x ∈ s ∧ φ x y) ∨
    ∃ ρ : PSet.{u}, IsOrd ρ ∧ ¬ ρ ≈ empty ∧ ¬ IsSucc ρ ∧ ¬ ρ ≈ omega ∧
      ∀ ν, ν ∈ ρ → ¬ Reach I ρ ν := by
  rcases em (∃ ρ, IsOrd ρ ∧ ¬ Good I ρ) with ⟨ρ, hρ, hg⟩ | hall
  · exact .inr ⟨ρ, hρ, fun h => hg (.inl h), fun h => hg (.inr (.inl h)),
      fun h => hg (.inr (.inr (.inl h))), fun ν hν h => hg (.inr (.inr (.inr ⟨ν, hν, h⟩)))⟩
  refine .inl fun s φ φ_resp φ_func => ?_
  have good : ∀ η, IsOrd η → Good I η := fun η hη =>
    (em _).resolve_right fun h => hall ⟨η, hη, h⟩
  have cls : ∀ η, IsOrd η → Cls I η := fun η hη =>
    ⟨hη, fun μ hμ => good μ (hμ.elim (fun h => hη.mem h) (fun e => hη.resp e.symm))⟩
  -- the ranks of the values
  let ψ : PSet.{u} → PSet.{u} → Prop := fun x η => ∃ y, φ x y ∧ η ≈ rank y
  have ⟨R, hR⟩ := (worldly_rule I_resp em s).replacement s rfl ψ
    (fun ex eη ⟨y, h1, h2⟩ => ⟨y, φ_resp ex (Equiv.refl _) h1, eη.symm.trans h2⟩)
    (fun hx ⟨y, h1, h2⟩ ⟨y', h1', h2'⟩ => h2.trans ((rank_congr (φ_func hx h1 h1')).trans h2'.symm))
    (fun _ ⟨y, _, h2⟩ => cls _ ((isOrd_rank y).resp h2.symm))
  let p : PSet.{u} → Prop := fun y => ∃ x, x ∈ s ∧ φ x y
  refine ⟨sep p (Vl R), fun y => (mem_sep fun y y' e ⟨x, hx, h⟩ =>
    ⟨x, hx, φ_resp (Equiv.refl _) e h⟩).trans ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩⟩
  have ⟨x, hx, hφ⟩ := h
  have hr : rank y ∈ R := (hR _).2 ⟨x, hx, y, hφ, Equiv.refl _⟩
  exact (mem_Vl em).2 ((mem_congr_left (isOrd_rank y).rank_equiv).1 (rank_mem hr))

#print axioms dichotomy
