import ConZF.ZF
/-!
The first-order instance of the dichotomy. `ISat η q x y`: `q` codes a formula `φ`, a number
`k` and a `k`-tuple of parameters, the free variables of `φ` are below `k+2`, and
`V_η ⊨ φ[x, y, params]`. An ordinal that is not `0`, not a successor, not `ω` and not reachable
for `ISat` is a limit above `ω`, and `V_ρ` is a model of `ZF`.
-/
universe u

namespace PSet
open Fml

/-- `k`-tuples, as nested pairs. -/
def tup : Nat → (Nat → PSet.{u}) → PSet.{u}
  | 0, _ => empty
  | k+1, e => pair (e 0) (tup k fun i => e (i+1))

theorem tup_inj : ∀ {k : Nat} {e e' : Nat → PSet.{u}}, tup k e ≈ tup k e' → ∀ i, i < k → e i ≈ e' i
  | 0, _, _, _, _, h => (Nat.not_lt_zero _ h).elim
  | _+1, _, _, h, 0, _ => (pair_inj h).1
  | _+1, _, _, h, i+1, hi => tup_inj (pair_inj h).2 i (Nat.lt_of_succ_lt_succ hi)

def ISat (η q x y : PSet.{u}) : Prop :=
  ∃ φ k e, q ≈ pair (enc φ) (pair (ofNat k) (tup k e)) ∧ Bound (k+2) φ ∧
    x ∈ Vl η ∧ y ∈ Vl η ∧ Sat (· ∈ Vl η) φ (Env.cons x (Env.cons y e))

section em
variable (em : ∀ p : Prop, p ∨ ¬p)
include em

theorem Vl_congr {η η' : PSet.{u}} (e : η ≈ η') : Vl η ≈ Vl η' :=
  ext fun _ => (mem_Vl em).trans <| (mem_congr_right (rank_congr e)).trans (mem_Vl em).symm

theorem ISat_resp {η η' q q' x x' y y' : PSet.{u}} (eη : η ≈ η') (eq : q ≈ q') (ex : x ≈ x')
    (ey : y ≈ y') (h : ISat η q x y) : ISat η' q' x' y' :=
  have ⟨φ, k, e, hq, hb, hx, hy, hs⟩ := h
  have eV := Vl_congr em eη
  ⟨φ, k, e, eq.symm.trans hq, hb, (mem_congr_right eV).1 ((mem_congr_left ex).1 hx),
    (mem_congr_right eV).1 ((mem_congr_left ey).1 hy),
    (Sat.resp_iff (fun _ => mem_congr_right eV) φ
      (Env.cons_resp ex (Env.cons_resp ey fun _ => Equiv.refl _))).1 hs⟩

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
    (ha : rank a ∈ ofNat m) (hb : rank b ∈ ofNat n) : rank (pair a b) ∈ ofNat (Fml.nmax m n + 2) :=
  rank_pair_mem em (isOrd_ofNat _) (ofNat_mono (Fml.le_nmax_left m n) ha)
    (ofNat_mono (Fml.le_nmax_right m n) hb)

theorem rank_enc_mem (em : ∀ p : Prop, p ∨ ¬p) : ∀ φ : Fml, ∃ n, rank (enc.{u} φ) ∈ ofNat n
  | .mem i j | .eq i j => ⟨_, rank_pair_ofNat em (rank_ofNat_mem _)
      (rank_pair_ofNat em (rank_ofNat_mem i) (rank_ofNat_mem j))⟩
  | .fls => ⟨_, rank_pair_ofNat em (rank_ofNat_mem 2) (n := 1)
      ((mem_congr_left (isOrd_empty.rank_equiv)).2 (mem_succ.2 (.inr (Equiv.refl _))))⟩
  | .all φ => have ⟨_, h⟩ := rank_enc_mem em φ
      ⟨_, rank_pair_ofNat em (rank_ofNat_mem _) h⟩
  | .imp φ ψ => have ⟨_, h1⟩ := rank_enc_mem em φ; have ⟨_, h2⟩ := rank_enc_mem em ψ
      ⟨_, rank_pair_ofNat em (rank_ofNat_mem _) (rank_pair_ofNat em h1 h2)⟩

theorem mem_succN {R x : PSet.{u}} (h : x ∈ R) : ∀ n, x ∈ succN n R
  | 0 => h
  | n+1 => mem_succ.2 (.inl (mem_succN h n))

def tupN : Nat → Nat
  | 0 => 1
  | k+1 => tupN k + 2

theorem rank_tup_mem (em : ∀ p : Prop, p ∨ ¬p) {R : PSet.{u}} (hR : IsOrd R) :
    ∀ {k : Nat} {e : Nat → PSet.{u}}, (∀ i, i < k → rank (e i) ∈ R) →
      rank (tup k e) ∈ succN (tupN k) R
  | 0, _, _ => rank_mem_succ em hR fun _ h => (not_mem_empty _ h).elim
  | k+1, _, h =>
    rank_pair_mem em (hR.iterate_succ (tupN k)) (mem_succN (h 0 (Nat.succ_pos k)) _)
      (rank_tup_mem em hR fun i hi => h (i+1) (Nat.succ_lt_succ hi))

/-! ### The second horn -/

section
variable (em : ∀ p : Prop, p ∨ ¬p) {ρ : PSet.{u}} (hρ : IsOrd ρ) (h0 : ¬ ρ ≈ empty)
  (hs : ¬ IsSucc ρ) (hω : ¬ ρ ≈ omega)
include em hρ h0 hs hω

omit h0 hs hω in
theorem rank_lt_of_mem {z : PSet.{u}} (hz : z ∈ Vl ρ) : rank z ∈ ρ :=
  (mem_congr_right hρ.rank_equiv).1 ((mem_Vl em).1 hz)

omit h0 hs hω in
theorem mem_Vl_of_rank {z : PSet.{u}} (hz : rank z ∈ ρ) : z ∈ Vl ρ :=
  (mem_Vl em).2 ((mem_congr_right hρ.rank_equiv).2 hz)

omit h0 hω in
/-- A set all of whose elements have rank below some `R ∈ ρ` is in `V_ρ`. -/
theorem mem_Vl_of_bound {y R : PSet.{u}} (hR : R ∈ ρ) (h : ∀ z, z ∈ y → rank z ∈ R) :
    y ∈ Vl ρ :=
  mem_Vl_of_rank em hρ <| hρ.trans _ (limit_succ_mem em hρ hs hR) _
    (rank_mem_succ em (hρ.mem hR) h)

/-- Finitely many elements of `V_ρ` have ranks below some `R ∈ ρ`. -/
theorem exists_bound_tup : ∀ (k : Nat) (e : Nat → PSet.{u}), (∀ i, i < k → e i ∈ Vl ρ) →
    ∃ R, R ∈ ρ ∧ ∀ i, i < k → rank (e i) ∈ R
  | 0, _, _ => ⟨omega, omega_mem em hρ h0 hs hω, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | k+1, e, he => by
    have ⟨R, hR, h⟩ := exists_bound_tup k e fun i hi => he i (Nat.lt_succ_of_lt hi)
    have ⟨R', hR', h1, h2⟩ := exists_upper em hρ hR
      (limit_succ_mem em hρ hs (rank_lt_of_mem em hρ (he k (Nat.lt_succ_self k))))
    refine ⟨R', hR', fun i hi => ?_⟩
    rcases Nat.lt_or_ge i k with hi' | hi'
    · exact h1 _ (h i hi')
    · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) hi'
      exact h2 _ (mem_succ.2 (.inr (Equiv.refl _)))

theorem Vl_model (hr : ∀ ν, ν ∈ ρ → ¬ Reach ISat ρ ν) : ZFModel (· ∈ Vl ρ) := by
  have hωρ := omega_mem em hρ h0 hs hω
  have Vρ : ∀ {y R : PSet.{u}}, R ∈ ρ → (∀ z, z ∈ y → rank z ∈ R) → y ∈ Vl ρ :=
    fun hR h => mem_Vl_of_bound em hρ hs hR h
  have rρ : ∀ {z}, z ∈ Vl ρ → rank z ∈ ρ := rank_lt_of_mem em hρ
  refine ⟨fun hx hz => Vl_trans em hx hz, ?_, fun hx hy => ?_, fun hx => ?_, fun hx => ?_, ?_,
    fun P x hx => ?_, fun ψ e he a ha hf => ?_⟩
  · exact Vρ hωρ fun _ h => (not_mem_empty _ h).elim
  · have ⟨R, hR, h1, h2⟩ := exists_upper em hρ (limit_succ_mem em hρ hs (rρ hx))
      (limit_succ_mem em hρ hs (rρ hy))
    exact Vρ hR fun z hz => (mem_upair.1 hz).elim
      (fun e => h1 _ (mem_succ.2 (.inr (rank_congr e))))
      (fun e => h2 _ (mem_succ.2 (.inr (rank_congr e))))
  · exact Vρ (rρ hx) fun z hz =>
      have ⟨w, hw, hzw⟩ := mem_sUnion.1 hz
      (isOrd_rank _).trans _ (rank_mem hw) _ (rank_mem hzw)
  · exact Vρ (limit_succ_mem em hρ hs (rρ hx)) fun z hz =>
      rank_mem_succ em (isOrd_rank _) fun w hw => rank_mem (mem_powerset.1 hz w hw)
  · exact mem_Vl_of_rank em hρ ((mem_congr_left isOrd_omega.rank_equiv).2 hωρ)
  · exact Vρ (rρ hx) fun _ ⟨⟨i, _⟩, e⟩ => rank_mem ⟨i, e⟩
  -- replacement
  have ⟨m, hm⟩ := exists_bound ψ
  have hb : Bound (m+2) ψ := hm.mono (Nat.le_add_right m 2)
  let q := pair (enc ψ) (pair (ofNat m) (tup m e))
  -- a bound `ν ∈ ρ` for the ranks of `q` and `a`
  have ⟨R0, hR0, hR0e⟩ := exists_bound_tup em hρ h0 hs hω m e fun i _ => he i
  have ⟨R1, hR1, hR0R1, hωR1⟩ := exists_upper em hρ hR0 hωρ
  have ⟨R, hR, hR1R, haR⟩ := exists_upper em hρ hR1 (limit_succ_mem em hρ hs (rρ ha))
  have hRo : IsOrd R := hρ.mem hR
  let T := succN (tupN m) R
  have hTo : IsOrd T := hRo.iterate_succ _
  have hT : T ∈ ρ := by
    suffices ∀ n, succN n R ∈ ρ from this _
    intro n; induction n with
    | zero => exact hR
    | succ n ih => exact limit_succ_mem em hρ hs ih
  have hRT : ∀ {z}, z ∈ R → z ∈ T := fun h => mem_succN h _
  have ⟨n, hn⟩ := rank_enc_mem em ψ
  have hω' : ∀ {z}, z ∈ omega → z ∈ T := fun h => hRT (hR1R _ (hωR1 _ h))
  have hq : rank q ∈ succN 4 T :=
    rank_pair_mem em hTo.succ.succ
      (mem_succ.2 (.inl (mem_succ.2 (.inl (hω' (isOrd_omega.trans _
        (mem_omega.2 ⟨n, Equiv.refl _⟩) _ hn))))))
      (rank_pair_mem em hTo
        (hω' ((mem_congr_left (isOrd_ofNat m).rank_equiv).2 (mem_omega.2 ⟨m, Equiv.refl _⟩)))
        (rank_tup_mem em hRo fun i hi => hR1R _ (hR0R1 _ (hR0e i hi))))
  let ν := succN 5 T
  have hν : ν ∈ ρ := by
    suffices ∀ k, succN k T ∈ ρ from this 5
    intro k; induction k with
    | zero => exact hT
    | succ k ih => exact limit_succ_mem em hρ hs ih
  have haν : rank a ∈ ν :=
    mem_succN (hRT (haR _ (mem_succ.2 (.inr (Equiv.refl _))))) 5
  have hqν : rank q ∈ ν := mem_succ.2 (.inl hq)
  -- the relation, and its instances of `ISat`
  let Rl : PSet.{u} → PSet.{u} → Prop := fun x y => Sat (· ∈ Vl ρ) ψ (Env.cons x (Env.cons y e))
  have hI : ∀ {x y}, x ∈ a → y ∈ Vl ρ → Rl x y → ISat ρ q x y :=
    fun hx hy h => ⟨ψ, m, e, Equiv.refl _, hb, Vl_trans em ha hx, hy, h⟩
  have hI' : ∀ {x y}, ISat ρ q x y → y ∈ Vl ρ ∧ Rl x y := by
    rintro x y ⟨φ, k, e', eq, hb', _, hy, h⟩
    have ⟨e1, e2⟩ := pair_inj eq
    cases enc_inj e1
    have ⟨e3, e4⟩ := pair_inj e2
    cases ofNat_inj e3
    refine ⟨hy, (sat_bound hb fun i hi => ?_).2 h⟩
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact tup_inj e4 i (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))
  have notunb : ¬ ∀ ζ, ζ ∈ ρ → ∃ x y, x ∈ a ∧ ISat ρ q x y ∧ ζ ∈ succ (rank y) :=
    fun h => hr ν hν ⟨q, a, hqν, haν,
      fun x y y' hx h1 h2 =>
        have ⟨hy, s1⟩ := hI' h1; have ⟨hy', s2⟩ := hI' h2; hf x y y' hx hy hy' s1 s2,
      fun _ _ _ h1 => rρ (hI' h1).1, h⟩
  have ⟨ζ, hζ, hbd⟩ : ∃ ζ, ζ ∈ ρ ∧ ¬ ∃ x y, x ∈ a ∧ ISat ρ q x y ∧ ζ ∈ succ (rank y) :=
    (em _).resolve_right fun h => notunb fun ζ hζ =>
      (em _).resolve_right fun h' => h ⟨ζ, hζ, h'⟩
  have hζo : IsOrd ζ := hρ.mem hζ
  have bound : ∀ {x y}, x ∈ a → y ∈ Vl ρ → Rl x y → rank y ∈ ζ := by
    intro x y hx hy h
    rcases (isOrd_rank y).trichotomy em hζo with h' | e' | h'
    · exact h'
    · exact (hbd ⟨x, y, hx, hI hx hy h, mem_succ.2 (.inr e'.symm)⟩).elim
    · exact (hbd ⟨x, y, hx, hI hx hy h, mem_succ.2 (.inl h')⟩).elim
  refine ⟨Vl ζ, Vρ hζ fun z hz => (mem_congr_right hζo.rank_equiv).1 ((mem_Vl em).1 hz),
    fun x y hx hy h => (mem_Vl em).2 ((mem_congr_right hζo.rank_equiv).2 (bound hx hy h))⟩

end

/-! ### The first horn -/

theorem V_model (hrepl : ∀ (s : PSet.{u}) (φ : PSet.{u} → PSet.{u} → Prop),
      (∀ {x x' y y'}, x ≈ x' → y ≈ y' → φ x y → φ x' y') →
      (∀ {x y y'}, x ∈ s → φ x y → φ x y' → y ≈ y') →
      ∃ img : PSet.{u}, ∀ y, y ∈ img ↔ ∃ x, x ∈ s ∧ φ x y) :
    ZFModel (fun _ : PSet.{u} => True) := by
  refine ⟨fun _ _ => trivial, trivial, fun _ _ => trivial, fun _ => trivial, fun _ => trivial,
    trivial, fun _ _ _ => trivial, fun ψ e _ a _ hf => ?_⟩
  have ⟨b, hb⟩ := hrepl a (fun x y => Sat (fun _ => True) ψ (Env.cons x (Env.cons y e)))
    (fun ex ey h => Sat.resp ψ (Env.cons_resp ex (Env.cons_resp ey fun _ => Equiv.refl _)) h)
    (fun hx h1 h2 => hf _ _ _ hx trivial trivial h1 h2)
  exact ⟨b, trivial, fun x y hx _ h => (hb y).2 ⟨x, hx, h⟩⟩

/-- **Lean without choice, with excluded middle, proves the consistency of `ZF`.** The model
is the sets-as-trees if they satisfy Replacement, and otherwise `V_ρ` for an ordinal `ρ` that
is not reachable by the definability rule. -/
theorem con_ZF (em : ∀ p : Prop, p ∨ ¬p) : Con ZF := by
  rcases dichotomy ISat.{0} em (ISat_resp em) with h | ⟨ρ, hρ, h0, hs, hω, hr⟩
  · exact (V_model h).con em
  · exact (Vl_model em hρ h0 hs hω hr).con em

/-- info: 'PSet.con_ZF' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZF
