import ConZF.PSet
/-
The materializing recursion (paper3, section "Accessibility on a big carrier gives
Replacement"). Differences from the paper, all simplifications: paths are lists of labels
(a big type) instead of nested pairs in `V`, so nothing needs to be decoded; targets are
arbitrary sets instead of ordinals; and the operation `D` (in the paper: the well-orderings of
subsets of `G ∪ ω`) is an arbitrary parameter.
-/
universe u

namespace PSet

/-- Labels of children: the child `a`, whose value `G` is computed first; the children
`b w` for `w ∈ D G`; and the children `c x` for `x` in a parameter set. -/
inductive Label : Type (u+1)
  | a
  | b (w : PSet.{u})
  | c (x : PSet.{u})

inductive Label.Equiv : Label.{u} → Label.{u} → Prop
  | a : Label.Equiv .a .a
  | b {w w'} : w ≈ w' → Label.Equiv (.b w) (.b w')
  | c {x x'} : x ≈ x' → Label.Equiv (.c x) (.c x')

/-- A path, deepest label first. The carrier of the recursion; it lives in `Type (u+1)`,
the same universe as `PSet.{u}`. -/
abbrev Path := List Label.{u}

variable (D : PSet.{u} → PSet.{u}) (U : PSet.{u})

section step
variable (R : Path.{u} → Path.{u} → Prop) (p : Path.{u})
  (rec : (c : Path.{u}) → R c p → PSet.{u})

/-- A guarded recursive call: `succ (rec (l :: p))` if `l :: p` is below `p`, else `∅`. -/
def call (l : Label.{u}) : PSet.{u} := guard (R (l :: p) p) fun h => succ (rec (l :: p) h)

/-- The value of the first call, or `∅`. -/
def stepG : PSet.{u} := guard (R (.a :: p) p) fun h => rec (.a :: p) h

/-- The step of the recursion. The second family of calls is indexed by the index type of
`D G`, where `G` is the value of the first call. -/
def step : PSet.{u} :=
  union (call R p rec .a) <| union
    (iUnion fun i : (D (stepG R p rec)).Idx => call R p rec (.b ((D (stepG R p rec)).Func i)))
    (iUnion fun j : U.Idx => call R p rec (.c (U.Func j)))

end step

/-- The materializing recursion: `Acc`-recursion on the big carrier `Path`, with motive
the big type `PSet`. -/
def F (R : Path.{u} → Path.{u} → Prop) (p : Path.{u}) (acc : Acc R p) : PSet.{u} :=
  Acc.rec (motive := fun _ _ => PSet.{u}) (fun p _ ih => step D U R p ih) acc

theorem F_eq (R) (p : Path.{u}) (acc : Acc R p) :
    F D U R p acc = step D U R p fun c h => F D U R c (acc.inv h) := by
  cases acc; rfl

/-! ### Target assignments -/

/-- The relation of a target assignment: `c` is a child of `p` and has a target. -/
def Rel (τ : Path.{u} → PSet.{u} → Prop) (c p : Path.{u}) : Prop :=
  ∃ l, c = l :: p ∧ ∃ t, τ c t

/-- `G` is the target of the child `a` of `p`, or empty if there is none. -/
def IsG (τ : Path.{u} → PSet.{u} → Prop) (p : Path.{u}) (G : PSet.{u}) : Prop :=
  ∀ x, x ∈ G ↔ ∃ ζ, τ (.a :: p) ζ ∧ x ∈ ζ

/-- The labels the step enumerates when the first call returns `G`. -/
def Avail (G : PSet.{u}) (l : Label.{u}) : Prop :=
  l = .a ∨ (∃ w, w ∈ D G ∧ l.Equiv (.b w)) ∨ ∃ x, x ∈ U ∧ l.Equiv (.c x)

/-- A coherent target assignment. It is a proposition about a relation; no part of it is
data. -/
structure Coherent (τ : Path.{u} → PSet.{u} → Prop) : Prop where
  /-- targets are determined up to bisimulation -/
  resp : ∀ {p t t'}, τ p t → t ≈ t' → τ p t'
  func : ∀ {p t t'}, τ p t → τ p t' → t ≈ t'
  /-- the assignment does not see the representation of a label -/
  lab : ∀ {l l' p t}, Label.Equiv l l' → τ (l :: p) t → τ (l' :: p) t
  /-- the target of a child is an element of the target of its parent -/
  desc : ∀ {l p t t'}, τ (l :: p) t → τ p t' → t ∈ t'
  /-- a target is the union of the successors of the targets of the available children -/
  sup : ∀ {p t G}, τ p t → IsG τ p G →
    ∀ x, x ∈ t ↔ ∃ l t', Avail D U G l ∧ τ (l :: p) t' ∧ x ∈ succ t'

variable {D U}

/-- What the step computes, given that the recursive calls return the targets. -/
theorem mem_step_iff {τ : Path.{u} → PSet.{u} → Prop} (hτ : Coherent D U τ) {p : Path.{u}}
    {rec : (c : Path.{u}) → Rel τ c p → PSet.{u}}
    (hrec : ∀ c h t, τ c t → rec c h ≈ t) (x : PSet.{u}) :
    x ∈ step D U (Rel τ) p rec ↔
      ∃ l t', Avail D U (stepG (Rel τ) p rec) l ∧ τ (l :: p) t' ∧ x ∈ succ t' := by
  have hcall : ∀ l, x ∈ call (Rel τ) p rec l ↔ ∃ t', τ (l :: p) t' ∧ x ∈ succ t' := by
    intro l
    refine mem_guard.trans ⟨?_, ?_⟩
    · rintro ⟨h, hx⟩
      have ⟨_, _, t', ht'⟩ := h
      exact ⟨t', ht', (mem_succ_congr (hrec _ h _ ht')).1 hx⟩
    · rintro ⟨t', ht', hx⟩
      have h : Rel τ (l :: p) p := ⟨l, rfl, t', ht'⟩
      exact ⟨h, (mem_succ_congr (hrec _ h _ ht')).2 hx⟩
  refine mem_union.trans <|
    (or_congr_right <| mem_union.trans <| or_congr mem_iUnion mem_iUnion).trans ⟨?_, ?_⟩
  · rintro (h | ⟨i, h⟩ | ⟨j, h⟩)
    · have ⟨t', h1, h2⟩ := (hcall _).1 h
      exact ⟨_, t', .inl rfl, h1, h2⟩
    · have ⟨t', h1, h2⟩ := (hcall _).1 h
      exact ⟨_, t', .inr (.inl ⟨_, func_mem _ i, .b (Equiv.refl _)⟩), h1, h2⟩
    · have ⟨t', h1, h2⟩ := (hcall _).1 h
      exact ⟨_, t', .inr (.inr ⟨_, func_mem _ j, .c (Equiv.refl _)⟩), h1, h2⟩
  · rintro ⟨l, t', hl | ⟨w, ⟨i, e⟩, hl⟩ | ⟨y, ⟨j, e⟩, hl⟩, h1, h2⟩
    · subst hl
      exact .inl ((hcall _).2 ⟨t', h1, h2⟩)
    · refine .inr (.inl ⟨i, (hcall _).2 ⟨t', ?_, h2⟩⟩)
      cases hl with | b hl => exact hτ.lab (.b (hl.trans e)) h1
    · refine .inr (.inr ⟨j, (hcall _).2 ⟨t', ?_, h2⟩⟩)
      cases hl with | c hl => exact hτ.lab (.c (hl.trans e)) h1

theorem isG_stepG {τ : Path.{u} → PSet.{u} → Prop} {p : Path.{u}}
    {rec : (c : Path.{u}) → Rel τ c p → PSet.{u}}
    (hrec : ∀ c h t, τ c t → rec c h ≈ t) : IsG τ p (stepG (Rel τ) p rec) := by
  refine fun x => mem_guard.trans ⟨?_, ?_⟩
  · rintro ⟨h, hx⟩
    have ⟨_, _, ζ, hζ⟩ := h
    exact ⟨ζ, hζ, (mem_congr_right (hrec _ h _ hζ)).1 hx⟩
  · rintro ⟨ζ, hζ, hx⟩
    have h : Rel τ (.a :: p) p := ⟨_, rfl, ζ, hζ⟩
    exact ⟨h, (mem_congr_right (hrec _ h _ hζ)).2 hx⟩

/-- **Materialization.** If `τ` is coherent and `p` has the target `t`, then `p` is accessible
and the recursion returns `t`: a set specified by a proposition is the value of a term. -/
theorem materialize {τ : Path.{u} → PSet.{u} → Prop} (hτ : Coherent D U τ) :
    ∀ (t : PSet.{u}) (p : Path.{u}), τ p t →
      Acc (Rel τ) p ∧ ∀ acc', F D U (Rel τ) p acc' ≈ t := by
  intro t
  induction t using mem_induction with | _ t ih => ?_
  intro p hp
  have children : ∀ c, Rel τ c p → ∀ tc, τ c tc →
      Acc (Rel τ) c ∧ ∀ acc', F D U (Rel τ) c acc' ≈ tc := by
    rintro c ⟨l, rfl, _⟩ tc htc
    exact ih tc (hτ.desc htc hp) _ htc
  have acc : Acc (Rel τ) p := ⟨_, fun c h => have ⟨_, _, tc, htc⟩ := h; (children c h tc htc).1⟩
  refine ⟨acc, fun acc' => ext fun x => ?_⟩
  rw [F_eq]
  have hrec : ∀ c (h : Rel τ c p) tc, τ c tc → F D U (Rel τ) c (acc'.inv h) ≈ tc :=
    fun c h tc htc => (children c h tc htc).2 _
  exact mem_step_iff hτ hrec _ |>.trans (hτ.sup hp (isG_stepG hrec) _).symm
