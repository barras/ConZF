# con-cic: plan and handover (2026-09-18)

## The claim being verified

**CIC₂ + EM with `Acc` on a big carrier interprets ZFC.** Hence Con(CIC₂+EM) → Con(ZF), so
ZF ⊬ Con(CIC₂+EM), and the project's original conjecture (ZF ⊢ Con(CIC_ω+EM)) is false for the
theory with unrestricted `Acc` (in particular for Lean minus `Classical.choice`, plus EM). No
choice or description operator is involved: large elimination of `Acc` over a carrier as big
as the motive turns an ordinal that is only *specified by a proposition* into the *value of a
term* ("unique choice for ordinals"), and that is what Replacement needs in sets-as-trees.

Paper: `paper3/main.tex`, section "Accessibility on a big carrier gives Replacement"
(`sec:bigacc`). Lean: `lean/` (core Lean 4, toolchain v4.34.0-rc2, **no Mathlib on purpose**, so
that `#print axioms` is meaningful). Build: `cd lean && lake build` (run from `lean/`, not from
`/project`).

## The mechanism (what to keep in mind)

- V := `PSet.{u}` = W X:Type u. X (Aczel). Carrier of the recursion: `Path := List Label`,
  `Label = a | b (w : PSet) | c (x : PSet)`; it lives in `Type (u+1)` like `PSet` (big carrier,
  big motive).
- Step (`PSet.step`): call `rec` at child `a` (guarded) → value `G`; then call `rec` at the
  children `b w` for `w` enumerated from the index type of `D G` (**index computed from the
  value of a recursive call**: this adaptivity is exactly what defeated the three "inspection"
  attempts in paper3 §8), and at `c x` for `x` in a parameter set `U`. Every call is guarded by
  its proposition via `guard P t = ⋃_{h:P} t h` (replaces decidability; cf. Coq's
  ConstructiveEpsilon). Value = union of successors of the calls' values.
- A *target assignment* τ : Path → PSet → Prop is pure Prop. `Coherent D U τ` (fields `resp`,
  `func`, `lab`, `desc`, `sup`). `Rel τ c p := c = l :: p ∧ τ c defined`.
- `PSet.materialize`: coherent τ, τ p t ⇒ `Acc (Rel τ) p` and `F … p acc ≈ t`. Proof by
  ∈-induction on t.
- `PSet.replacement`: if the values of a functional relation φ on s lie in a class C with a
  *uniform* family of coherent assignments `T η` (root target η), then the image of s exists.
  The glued tree gives the root **no target** (its target would be the sup being constructed;
  the first paper sketch was circular here, the formalization caught it).

## Done (all compiled, axioms = [propext] only; no EM, no choice, no Quot.sound)

- `lean/ConCic/PSet.lean`: PSet, ≈, ∈, ext, ∈-induction, ∅, range, ⋃, guard, ∪, {·}, succ, sep.
- `lean/ConCic/Mat.lean`: Label, Path, step, `F`, `F_eq`, `Coherent`, `mem_step_iff`,
  `materialize`.
- `lean/ConCic/Repl.lean`: `Glue`, `glue_coherent`, `exists_sup`, `replacement`.
- `lean/ConCic/NatInstance.lean`: non-vacuity: finite ordinals have uniform coherent
  assignments (`natT_coherent`), giving `replacement_nat`. Of no set-theoretic interest.

## Not done: the set theory (this is the whole remaining risk)

Need: a class C of ordinals, closed enough that "Replacement for C-valued functions" yields a
model of ZF, together with a **uniformly definable** coherent assignment for every η ∈ C, for
a concrete term `D`. Paper's route:

1. `D G` := set of well-orderings of subsets of G ∪ ω (power set + separation; a term).
2. η is *type 1* if η ≤ ℵ(ζ ∪ ω) for some ζ < η; ζ(η) := least such. Assignment at a node
   with target η: child `a` ↦ ζ(η); child `b w` ↦ order type of w, when that is < η.
   Choice-free (needs EM for "least" and comparability of well-orders).
3. η not type 1 (above ω₁, closed under Hartogs): need a **definable** increasing cofinal
   c : μ → η, μ < η; child `a` ↦ μ, child `b w` ↦ c(otype w). No choice-free definition is
   known (uniformity is essential: choosing one certificate per a ∈ s is AC, and collecting all
   certificates is the Collection instance being proved). Paper: pass to L and take the
   <_L-least c. If no such c exists in L, η is regular in L, hence inaccessible in L (call the
   least one ρ) and L_ρ ⊨ ZFC. So: by EM, L ⊨ ZFC or L_ρ ⊨ ZFC.
4. Subtleties already noticed: (a) "L ⊨ Separation" needs reflection for the L-hierarchy, which
   needs Replacement in V; claim: the bounding principle just proved (ordinal-valued definable
   functions on a set are bounded) suffices, since that is all the reflection proof uses.
   **Check this.** (b) (|ζ|⁺)^L ≤ ℵ(ζ) and "regular limit cardinal of L ⇒ L_ρ ⊨ Power set" need
   condensation inside Z + ∈-recursion + the bounding principle. **Check.** (c) The ambient
   theory of V in intensional CIC₂+EM: Zermelo + ∈-recursion (paper2 did this for the
   *extensional* theory; Werner/Barras did Z in Coq). **Check what is actually needed.**

### Suggested order for whoever continues

A. (paper, 1–2 days of care) Write step 2–4 as real proofs, not a sketch. Decide whether the
   final statement is "ZFC interpretable in CIC₂+EM" (via L) or the cheaper and still decisive
   "CIC₂ + EM + (V has a definable global well-order, as a Prop hypothesis) ⊢ Replacement in V
   or there is an inaccessible", plus the remark that L satisfies the hypothesis.
B. (Lean, medium) Concrete `D` and the type-1 instance: ordinals in PSet, well-orders as sets
   of pairs (needs Kuratowski pairs + injectivity; not yet in `PSet.lean`), comparability,
   Hartogs. Goal: `Coherent D U (T η)` for all η below the least non-type-1 ordinal; then
   `replacement` gives bounding for functions into that class. EM will be needed: add it as
   an explicit hypothesis or a local `axiom em`, never `Classical.em` (which is choice).
C. (Lean, large) Global-well-order hypothesis version of step 3, then the dichotomy.
D. (Lean, very large; probably not worth it) L inside PSet.
E. Expected, unchecked: with n+2 universes, rank(V_level k) is a regular (so inaccessible)
   cardinal of V_level k+1, by the same recursion with a parameter from the higher level in R.
   That would match the ZFC + n inaccessibles lower bound of Lean-with-choice, without choice.

## Discipline

- `#print axioms` must never show `Classical.choice` or `sorryAx`. `by_cases`/`Decidable`
  without an instance, `open Classical`, `simp` lemmas about `ite` on Props, and most of
  Mathlib will pull choice in. Keep Mathlib out.
- Do not make any part of a target assignment data. τ, C, T, φ are Props/relations. The
  only data are s (a variable of type PSet), D (a term), and what `F` computes.
- The root of a glued tree has no target (see above).

## State of paper3 (what is stale)

- `sec:bigacc` is current, including the root fix and the formalization paragraph; the
  paper's Definition mat still uses nested pairs in V for paths and ordinal targets, while
  Lean uses lists of labels and arbitrary set targets. Align the paper with Lean (simpler).
- Abstract, note after Conjecture main, end of §8, Status: updated. Introduction and §3–6
  still argue towards the refuted conjecture; they need reframing: the oracle model and the
  proved cases are now about **small-carrier Acc** (theory CIC₂ˢ; Theorem cic2: ZF ⊢
  Con(CIC₂ˢ+EM), conditional on the rule-by-rule soundness check). If both results hold, the
  ZF boundary runs exactly between `Acc` on small and on big carriers. Title needs changing.
- Remaining open conjecture: ZF ⊢ Con(CIC_ω + EM with `Acc` on carriers in Type₀ only). Obstacle:
  kinds are not syntactic with >2 universes. W with big branching: no analogue of the
  counterexample known, not proved safe either.

## Context not in the repo

- A friend of Mario's has unpublished results: CIC⁻ (no Acc) with ω universes ≡ Z + {V_α exists :
  α < Ω}, Ω the proof-theoretic ordinal of MLTT+W+universes, via an assembly model, **without
  EM**; and Con(CIC⁻_ω) is provable in axiom-free CIC with 1–2 universes using Acc. Do not put
  these in a paper without Mario's say-so. They fit: Acc is where the strength is.
- Assembly models cannot support EM: paper1 Prop 4.4 (codiscrete Prop ⇒ any set-sized
  universe of assemblies has inaccessible size).
- Mario's working preferences: commit at stopping points, never push; `git commit -F file`;
  Edit tool rather than sed/python for ordinary edits; definitions before use, load-bearing
  definitions clause by clause; no formalization of things whose design is still moving.
