import ConCic.Fml
/-!
The first-order instance of the dichotomy. `ISat η q x y`: `q` codes a formula `ψ` and a
parameter `p`, and `V_η ⊨ ψ[x, y, p]`. An ordinal that is not `0`, not a successor, not `ω` and
not reachable for `ISat` has `V_ρ` closed under Replacement for first-order definable functions;
being a limit above `ω`, `V_ρ` then satisfies `ZF`.
-/
universe u

namespace PSet

def env3 (x y p : PSet.{u}) : Nat → PSet.{u} :=
  Env.cons x (Env.cons y (Env.cons p fun _ => empty))

theorem env3_resp {x x' y y' p p' : PSet.{u}} (ex : x ≈ x') (ey : y ≈ y') (ep : p ≈ p') :
    ∀ i, env3 x y p i ≈ env3 x' y' p' i
  | 0 => ex
  | 1 => ey
  | 2 => ep
  | _+3 => Equiv.refl _

def ISat (η q x y : PSet.{u}) : Prop :=
  ∃ φ p, q ≈ pair (enc φ) p ∧ x ∈ Vl η ∧ y ∈ Vl η ∧ p ∈ Vl η ∧ Sat (Vl η) φ (env3 x y p)

section em
variable (em : ∀ p : Prop, p ∨ ¬p)
include em

theorem Vl_congr {η η' : PSet.{u}} (e : η ≈ η') : Vl η ≈ Vl η' :=
  ext fun _ => (mem_Vl em).trans <| (mem_congr_right (rank_congr e)).trans (mem_Vl em).symm

theorem ISat_resp {η η' q q' x x' y y' : PSet.{u}} (eη : η ≈ η') (eq : q ≈ q') (ex : x ≈ x')
    (ey : y ≈ y') (h : ISat η q x y) : ISat η' q' x' y' :=
  have ⟨φ, p, hq, hx, hy, hp, hs⟩ := h
  have eV := Vl_congr em eη
  ⟨φ, p, eq.symm.trans hq, (mem_congr_right eV).1 ((mem_congr_left ex).1 hx),
    (mem_congr_right eV).1 ((mem_congr_left ey).1 hy), (mem_congr_right eV).1 hp,
    Sat.resp eV φ (env3_resp ex ey (Equiv.refl _)) hs⟩

theorem Vl_trans {ρ y z : PSet.{u}} (hy : y ∈ Vl ρ) (hz : z ∈ y) : z ∈ Vl ρ :=
  (mem_Vl em).2 ((isOrd_rank ρ).trans _ ((mem_Vl em).1 hy) _ (rank_mem hz))

theorem limit_succ_mem {ρ ζ : PSet.{u}} (hρ : IsOrd ρ) (hs : ¬ IsSucc ρ) (hζ : ζ ∈ ρ) :
    succ ζ ∈ ρ := by
  refine ((hρ.mem hζ).succ.subset em hρ fun z hz => ?_).resolve_right fun e => hs ⟨ζ, e.symm⟩
  rcases mem_succ.1 hz with hz | e
  · exact hρ.trans ζ hζ z hz
  · exact (mem_congr_left e).2 hζ

theorem omega_mem {ρ : PSet.{u}} (hρ : IsOrd ρ) (h0 : ¬ ρ ≈ empty) (hs : ¬ IsSucc ρ)
    (hω : ¬ ρ ≈ omega) : omega ∈ ρ := by
  rcases isOrd_omega.trichotomy em hρ with h | e | h
  · exact h
  · exact (hω e.symm).elim
  · have ⟨n, e⟩ := mem_omega.1 h
    cases n with
    | zero => exact (h0 e).elim
    | succ n => exact (hs ⟨ofNat n, e⟩).elim

/-- Two elements of an ordinal are included in a third. -/
theorem exists_upper {ρ a b : PSet.{u}} (hρ : IsOrd ρ) (ha : a ∈ ρ) (hb : b ∈ ρ) :
    ∃ R, R ∈ ρ ∧ (∀ z, z ∈ a → z ∈ R) ∧ (∀ z, z ∈ b → z ∈ R) := by
  rcases (hρ.mem ha).trichotomy em (hρ.mem hb) with h | e | h
  · exact ⟨b, hb, fun z hz => (hρ.mem hb).trans a h z hz, fun _ hz => hz⟩
  · exact ⟨b, hb, fun _ hz => (mem_congr_right e).1 hz, fun _ hz => hz⟩
  · exact ⟨a, ha, fun _ hz => hz, fun z hz => (hρ.mem ha).trans b h z hz⟩

end em

theorem ofNat_mono {x : PSet.{u}} : ∀ {m n : Nat}, m ≤ n → x ∈ ofNat m → x ∈ ofNat n
  | _, 0, h, hx => by cases Nat.le_zero.1 h; exact hx
  | m, n+1, h, hx => by
    rcases Nat.lt_or_ge n m with h' | h'
    · cases Nat.le_antisymm h (Nat.succ_le_of_lt h'); exact hx
    · exact mem_succ.2 (.inl (ofNat_mono h' hx))

theorem rank_ofNat_mem (n : Nat) : rank (ofNat.{u} n) ∈ ofNat (n+1) :=
  (mem_congr_left (isOrd_ofNat n).rank_equiv).2 (mem_succ.2 (.inr (Equiv.refl _)))

theorem rank_pair_ofNat (em : ∀ p : Prop, p ∨ ¬p) {a b : PSet.{u}} {m n : Nat}
    (ha : rank a ∈ ofNat m) (hb : rank b ∈ ofNat n) : rank (pair a b) ∈ ofNat (max m n + 2) :=
  rank_pair_mem em (isOrd_ofNat _) (ofNat_mono (Nat.le_max_left m n) ha)
    (ofNat_mono (Nat.le_max_right m n) hb)

theorem rank_enc_mem (em : ∀ p : Prop, p ∨ ¬p) : ∀ φ : Fml, ∃ n, rank (enc.{u} φ) ∈ ofNat n
  | .mem i j | .eq i j => ⟨_, rank_pair_ofNat em (rank_ofNat_mem _)
      (rank_pair_ofNat em (rank_ofNat_mem i) (rank_ofNat_mem j))⟩
  | .neg φ | .all φ => have ⟨_, h⟩ := rank_enc_mem em φ
      ⟨_, rank_pair_ofNat em (rank_ofNat_mem _) h⟩
  | .and φ ψ => have ⟨_, h1⟩ := rank_enc_mem em φ; have ⟨_, h2⟩ := rank_enc_mem em ψ
      ⟨_, rank_pair_ofNat em (rank_ofNat_mem _) (rank_pair_ofNat em h1 h2)⟩

/-- **The second horn, first-order.** If `ρ` is an ordinal that is not `0`, not a successor, not
`ω`, and not reachable for `ISat`, then `V_ρ` is closed under images of functions defined over
`V_ρ` by a formula with a parameter in `V_ρ`. -/
theorem unreachable_replacement (em : ∀ p : Prop, p ∨ ¬p) {ρ : PSet.{u}} (hρ : IsOrd ρ)
    (h0 : ¬ ρ ≈ empty) (hs : ¬ IsSucc ρ) (hω : ¬ ρ ≈ omega)
    (hr : ∀ ν, ν ∈ ρ → ¬ Reach ISat ρ ν)
    (ψ : Fml) {p s : PSet.{u}} (hp : p ∈ Vl ρ) (hsV : s ∈ Vl ρ)
    (hf : ∀ x y y', x ∈ s → y ∈ Vl ρ → y' ∈ Vl ρ →
      Sat (Vl ρ) ψ (env3 x y p) → Sat (Vl ρ) ψ (env3 x y' p) → y ≈ y') :
    ∃ img, img ∈ Vl ρ ∧
      ∀ y, y ∈ img ↔ ∃ x, x ∈ s ∧ y ∈ Vl ρ ∧ Sat (Vl ρ) ψ (env3 x y p) := by
  have rρ : ∀ {z}, z ∈ Vl ρ → rank z ∈ ρ := fun hz =>
    (mem_congr_right hρ.rank_equiv).1 ((mem_Vl em).1 hz)
  let q := pair (enc ψ) p
  -- a bound `ν ∈ ρ` for the ranks of `q` and `s`
  have hωρ := omega_mem em hρ h0 hs hω
  have ⟨R1, hR1, hp1, hs1⟩ := exists_upper em hρ
    (limit_succ_mem em hρ hs (rρ hp)) (limit_succ_mem em hρ hs (rρ hsV))
  have ⟨R, hR, h1R, hωR⟩ := exists_upper em hρ hR1 hωρ
  have hRo : IsOrd R := hρ.mem hR
  have ⟨n, hn⟩ := rank_enc_mem em ψ
  have hq : rank q ∈ succ (succ R) := rank_pair_mem em hRo
    (hωR _ (isOrd_omega.trans _ (mem_omega.2 ⟨n, Equiv.refl _⟩) _ hn))
    (h1R _ (hp1 _ (mem_succ.2 (.inr (Equiv.refl _)))))
  let ν := succ (succ (succ R))
  have hν : ν ∈ ρ := limit_succ_mem em hρ hs (limit_succ_mem em hρ hs (limit_succ_mem em hρ hs hR))
  have hsν : rank s ∈ ν :=
    mem_succ.2 (.inl (mem_succ.2 (.inl (mem_succ.2 (.inl (h1R _ (hs1 _ (mem_succ.2 (.inr (Equiv.refl _))))))))))
  -- so `(q, s)` is not unbounded; it is functional and has values in `V_ρ`
  have hI : ∀ {x y}, x ∈ s → y ∈ Vl ρ → Sat (Vl ρ) ψ (env3 x y p) → ISat ρ q x y :=
    fun hx hy h => ⟨ψ, p, Equiv.refl _, Vl_trans em hsV hx, hy, hp, h⟩
  have hI' : ∀ {x y}, ISat ρ q x y → y ∈ Vl ρ ∧ Sat (Vl ρ) ψ (env3 x y p) := by
    rintro x y ⟨φ, p', e, _, hy, _, h⟩
    have ⟨e1, e2⟩ := pair_inj e
    cases enc_inj e1
    exact ⟨hy, Sat.resp (Equiv.refl _) ψ (env3_resp (Equiv.refl _) (Equiv.refl _) e2.symm) h⟩
  have notunb : ¬ ∀ ζ, ζ ∈ ρ → ∃ x y, x ∈ s ∧ ISat ρ q x y ∧ ζ ∈ succ (rank y) :=
    fun h => hr ν hν ⟨q, s, mem_succ.2 (.inl hq), hsν,
      fun x y y' hx h1 h2 =>
        have ⟨hy, s1⟩ := hI' h1; have ⟨hy', s2⟩ := hI' h2; hf x y y' hx hy hy' s1 s2,
      fun _ _ _ h1 => rρ (hI' h1).1, h⟩
  have ⟨ζ, hζ, hb⟩ : ∃ ζ, ζ ∈ ρ ∧ ¬ ∃ x y, x ∈ s ∧ ISat ρ q x y ∧ ζ ∈ succ (rank y) :=
    (em _).resolve_right fun h => notunb fun ζ hζ =>
      (em _).resolve_right fun h' => h ⟨ζ, hζ, h'⟩
  have hζo : IsOrd ζ := hρ.mem hζ
  -- every value has rank below `ζ`
  have bound : ∀ {x y}, x ∈ s → y ∈ Vl ρ → Sat (Vl ρ) ψ (env3 x y p) → rank y ∈ ζ := by
    intro x y hx hy h
    rcases (isOrd_rank y).trichotomy em hζo with h' | e | h'
    · exact h'
    · exact (hb ⟨x, y, hx, hI hx hy h, mem_succ.2 (.inr e.symm)⟩).elim
    · exact (hb ⟨x, y, hx, hI hx hy h, mem_succ.2 (.inl h')⟩).elim
  let P : PSet.{u} → Prop := fun y => ∃ x, x ∈ s ∧ y ∈ Vl ρ ∧ Sat (Vl ρ) ψ (env3 x y p)
  have Presp : ∀ y y', y ≈ y' → P y → P y' := fun _ _ e ⟨x, hx, hy, h⟩ =>
    ⟨x, hx, (mem_congr_left e).1 hy,
      Sat.resp (Equiv.refl _) ψ (env3_resp (Equiv.refl _) e (Equiv.refl _)) h⟩
  have rζ : ∀ {z}, z ∈ Vl ζ → rank z ∈ ζ := fun hz =>
    (mem_congr_right hζo.rank_equiv).1 ((mem_Vl em).1 hz)
  refine ⟨sep P (Vl ζ), ?_, fun y => (mem_sep Presp).trans ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩⟩
  · have h1 : rank (sep P (Vl ζ)) ∈ succ ζ :=
      rank_mem_succ em hζo fun z hz => rζ ((mem_sep Presp).1 hz).1
    exact (mem_Vl em).2 ((mem_congr_right hρ.rank_equiv).2
      (hρ.trans _ (limit_succ_mem em hρ hs hζ) _ h1))
  · have ⟨x, hx, hy, h⟩ := h
    exact (mem_Vl em).2 ((mem_congr_right hζo.rank_equiv).2 (bound hx hy h))

/-- The dichotomy for first-order definability. -/
theorem dichotomy_fo (em : ∀ p : Prop, p ∨ ¬p) :
    (∀ (s : PSet.{u}) (φ : PSet.{u} → PSet.{u} → Prop),
      (∀ {x x' y y'}, x ≈ x' → y ≈ y' → φ x y → φ x' y') →
      (∀ {x y y'}, x ∈ s → φ x y → φ x y' → y ≈ y') →
      ∃ img : PSet.{u}, ∀ y, y ∈ img ↔ ∃ x, x ∈ s ∧ φ x y) ∨
    ∃ ρ : PSet.{u}, IsOrd ρ ∧ omega ∈ ρ ∧ (∀ ζ, ζ ∈ ρ → succ ζ ∈ ρ) ∧
      ∀ (ψ : Fml) (p s : PSet.{u}), p ∈ Vl ρ → s ∈ Vl ρ →
        (∀ x y y', x ∈ s → y ∈ Vl ρ → y' ∈ Vl ρ →
          Sat (Vl ρ) ψ (env3 x y p) → Sat (Vl ρ) ψ (env3 x y' p) → y ≈ y') →
        ∃ img, img ∈ Vl ρ ∧
          ∀ y, y ∈ img ↔ ∃ x, x ∈ s ∧ y ∈ Vl ρ ∧ Sat (Vl ρ) ψ (env3 x y p) := by
  refine (dichotomy ISat em (ISat_resp em)).imp id fun ⟨ρ, hρ, h0, hs, hω, hr⟩ =>
    ⟨ρ, hρ, omega_mem em hρ h0 hs hω, fun _ hζ => limit_succ_mem em hρ hs hζ,
      fun ψ _ _ hp hsV hf => unreachable_replacement em hρ h0 hs hω hr ψ hp hsV hf⟩

#print axioms dichotomy_fo
