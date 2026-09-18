import ConZF.ZF
/-!
Readback of the axioms of `ZF`: what each one says in a class model `M`, in ordinary notation.
These lemmas are not used by the consistency proof; they are there to check that the de Bruijn
indices in `ZFAx` express the intended axioms, so that `Con ZF` means what it should.
-/
universe u

namespace PSet
open Fml

variable (em : ∀ p : Prop, p ∨ ¬p) {M : PSet.{u} → Prop} (e : Nat → PSet.{u})
include em

theorem sat_ext : Sat M ZFAx.ext e ↔
    ((∀ z, M z → (z ∈ e 0 ↔ z ∈ e 1)) → e 0 ≈ e 1) :=
  ⟨fun h h' => h fun z hz => (sat_iff em).2 (h' z hz),
   fun h h' => h fun z hz => (sat_iff em).1 (h' z hz)⟩

theorem sat_found : Sat M ZFAx.found e ↔
    ((∃ z, M z ∧ z ∈ e 0) → ∃ y, M y ∧ y ∈ e 0 ∧ ∀ z, M z → z ∈ y → ¬ z ∈ e 0) :=
  ⟨fun h h' =>
    have ⟨y, hy, h2⟩ := (sat_ex em).1 (h ((sat_ex em).2 h'))
    have ⟨a, b⟩ := (sat_and em).1 h2
    ⟨y, hy, a, b⟩,
   fun h h' =>
    have ⟨y, hy, a, b⟩ := h ((sat_ex em).1 h')
    (sat_ex em).2 ⟨y, hy, (sat_and em).2 ⟨a, b⟩⟩⟩

theorem sat_pair : Sat M ZFAx.pair e ↔ ∃ z, M z ∧ e 0 ∈ z ∧ e 1 ∈ z :=
  (sat_ex em).trans (exists_congr fun _ => and_congr Iff.rfl (sat_and em))

theorem sat_union : Sat M ZFAx.union e ↔
    ∃ u, M u ∧ ∀ y, M y → ∀ z, M z → z ∈ y → y ∈ e 0 → z ∈ u :=
  sat_ex em

theorem sat_power : Sat M ZFAx.power e ↔
    ∃ p, M p ∧ ∀ y, M y → (∀ z, M z → z ∈ y → z ∈ e 0) → y ∈ p :=
  sat_ex em

theorem sat_inf : Sat M ZFAx.inf e ↔
    ∃ w, M w ∧ (∃ o, M o ∧ o ∈ w ∧ ∀ z, M z → ¬ z ∈ o) ∧
      ∀ y, M y → y ∈ w → ∃ s, M s ∧ s ∈ w ∧ ∀ z, M z → (z ∈ s ↔ z ∈ y ∨ z ≈ y) := by
  refine (sat_ex em).trans (exists_congr fun w => and_congr Iff.rfl ((sat_and em).trans ?_))
  refine and_congr ((sat_ex em).trans (exists_congr fun _ => and_congr Iff.rfl (sat_and em))) ?_
  refine ⟨fun h y hy hyw => ?_, fun h y hy hyw => ?_⟩
  · have ⟨s, hs, h2⟩ := (sat_ex em).1 (h y hy hyw)
    have ⟨a, b⟩ := (sat_and em).1 h2
    exact ⟨s, hs, a, fun z hz => ((sat_iff em).1 (b z hz)).trans (sat_or em)⟩
  · have ⟨s, hs, a, b⟩ := h y hy hyw
    exact (sat_ex em).2 ⟨s, hs, (sat_and em).2 ⟨a, fun z hz =>
      (sat_iff em).2 ((b z hz).trans (sat_or em (M := M) (φ := mem 0 2) (ψ := eq 0 2)
        (e := Env.cons z (Env.cons s (Env.cons y (Env.cons w e))))).symm)⟩⟩

theorem sat_sep (ψ : Fml) : Sat M (ZFAx.sep ψ) e ↔
    ∃ y, M y ∧ ∀ z, M z → (z ∈ y ↔ z ∈ e 0 ∧ Sat M ψ (Env.cons z e)) := by
  refine (sat_ex em).trans (exists_congr fun y => and_congr Iff.rfl ?_)
  have H : ∀ z, Sat M (rename ZFAx.sepR ψ) (Env.cons z (Env.cons y e)) ↔
      Sat M ψ (Env.cons z e) := fun z =>
    (sat_rename ψ _ _).trans (Sat.resp_iff (fun _ => Iff.rfl) ψ fun i => by
      cases i <;> exact Equiv.refl _)
  refine ⟨fun h z hz => ((sat_iff em).1 (h z hz)).trans ((sat_and em).trans
      (and_congr Iff.rfl (H z))), fun h z hz => (sat_iff em).2 ((h z hz).trans ?_)⟩
  exact (and_congr Iff.rfl (H z).symm).trans
    (sat_and em (M := M) (φ := mem 0 2) (ψ := rename ZFAx.sepR ψ)
      (e := Env.cons z (Env.cons y e))).symm

theorem sat_repl (ψ : Fml) : Sat M (ZFAx.repl ψ) e ↔
    ((∀ x, M x → x ∈ e 0 → ∀ y, M y → ∀ y', M y' → Sat M ψ (Env.cons x (Env.cons y e)) →
        Sat M ψ (Env.cons x (Env.cons y' e)) → y ≈ y') →
      ∃ b, M b ∧ ∀ y, M y → (∃ x, M x ∧ x ∈ e 0 ∧ Sat M ψ (Env.cons x (Env.cons y e))) →
        y ∈ b) := by
  have E : ∀ (r : Nat → Nat) (E' E'' : Nat → PSet.{u}), (∀ i, E' (r i) ≈ E'' i) →
      (Sat M (rename r ψ) E' ↔ Sat M ψ E'') := fun r E' E'' h =>
    (sat_rename ψ r E').trans (Sat.resp_iff (fun _ => Iff.rfl) ψ h)
  have e1 : ∀ x y y', Sat M (rename ZFAx.r1 ψ) (Env.cons y' (Env.cons y (Env.cons x e))) ↔
      Sat M ψ (Env.cons x (Env.cons y e)) := fun _ _ _ =>
    E _ _ _ fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _
  have e2 : ∀ x y y', Sat M (rename ZFAx.r2 ψ) (Env.cons y' (Env.cons y (Env.cons x e))) ↔
      Sat M ψ (Env.cons x (Env.cons y' e)) := fun _ _ _ =>
    E _ _ _ fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _
  have e3 : ∀ x y b, Sat M (rename ZFAx.r3 ψ) (Env.cons x (Env.cons y (Env.cons b e))) ↔
      Sat M ψ (Env.cons x (Env.cons y e)) := fun _ _ _ =>
    E _ _ _ fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _
  -- the hypothesis
  have hyp : Sat M (all (imp (mem 0 1) (all (all (imp (rename ZFAx.r1 ψ)
        (imp (rename ZFAx.r2 ψ) (eq 1 0))))))) e ↔
      (∀ x, M x → x ∈ e 0 → ∀ y, M y → ∀ y', M y' → Sat M ψ (Env.cons x (Env.cons y e)) →
        Sat M ψ (Env.cons x (Env.cons y' e)) → y ≈ y') :=
    ⟨fun h x hx hxa y hy y' hy' h1 h2 =>
      h x hx hxa y hy y' hy' ((e1 x y y').2 h1) ((e2 x y y').2 h2),
     fun h x hx hxa y hy y' hy' h1 h2 =>
      h x hx hxa y hy y' hy' ((e1 x y y').1 h1) ((e2 x y y').1 h2)⟩
  -- the conclusion
  have con : Sat M (ex (all (imp (ex (and (mem 0 3) (rename ZFAx.r3 ψ))) (mem 0 1)))) e ↔
      ∃ b, M b ∧ ∀ y, M y → (∃ x, M x ∧ x ∈ e 0 ∧ Sat M ψ (Env.cons x (Env.cons y e))) →
        y ∈ b := by
    refine (sat_ex em).trans (exists_congr fun b => and_congr Iff.rfl ?_)
    have inner : ∀ y, Sat M (ex (and (mem 0 3) (rename ZFAx.r3 ψ)))
          (Env.cons y (Env.cons b e)) ↔
        ∃ x, M x ∧ x ∈ e 0 ∧ Sat M ψ (Env.cons x (Env.cons y e)) := fun y =>
      (sat_ex em).trans (exists_congr fun x => and_congr Iff.rfl
        ((sat_and em).trans (and_congr Iff.rfl (e3 x y b))))
    exact ⟨fun h y hy h' => h y hy ((inner y).2 h'), fun h y hy h' => h y hy ((inner y).1 h')⟩
  exact ⟨fun h h' => con.1 (h (hyp.2 h')), fun h h' => con.2 (h (hyp.1 h'))⟩
