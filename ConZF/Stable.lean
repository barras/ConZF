import ConZF.FirstOrder
/-!
How much of excluded middle is used. `Con ZF` is a negation, so it follows from the double
negation of excluded middle, which is the same as the double negation shift
`(∀ x, ¬¬A x) → ¬¬∀ x, A x`. Whether it holds with no hypothesis at all is open; see the
discussion in `doc/main.tex`.
-/
universe u

namespace PSet

/-- `Con ZF` from the irrefutability of excluded middle. -/
theorem con_ZF_of_not_not_em (h : ¬¬∀ p : Prop, p ∨ ¬p) : Con ZF :=
  fun d => h fun em => con_ZF em d

/-- The double negation shift, for predicates on an arbitrary sort. -/
def DNS : Prop := ∀ {α : Sort u} (A : α → Prop), (∀ x, ¬¬A x) → ¬¬∀ x, A x

theorem not_not_em_of_dns (dns : ∀ A : Prop → Prop, (∀ x, ¬¬A x) → ¬¬∀ x, A x) :
    ¬¬∀ p : Prop, p ∨ ¬p :=
  dns (fun p => p ∨ ¬p) fun _ h => h (.inr fun hp => h (.inl hp))

theorem dns_of_not_not_em (h : ¬¬∀ p : Prop, p ∨ ¬p) : DNS.{u} :=
  fun A hA hn => h fun em => hn fun x => (em (A x)).resolve_right (hA x)

theorem con_ZF_of_dns (dns : DNS.{1}) : Con ZF :=
  con_ZF_of_not_not_em (not_not_em_of_dns fun A => dns A)

/-! ### Why accessibility is the obstruction

Accessibility is not a stable proposition. For the search relation of a decidable predicate,
the root is accessible iff a witness exists, so "classically well-founded implies accessible"
is Markov's principle, and "classically well-founded implies not not accessible", for a node
with one such search tree below each child, is the double negation shift for `∀ n, ∃ k`. -/

/-- The search relation of `P`: `n + 1` is below `n` as long as `P n` fails. -/
def Search (P : Nat → Prop) (m n : Nat) : Prop := m = n + 1 ∧ ¬P n

theorem exists_of_acc_search {P : Nat → Prop} [DecidablePred P] {n : Nat}
    (h : Acc (Search P) n) : ∃ k, P k := by
  induction h with
  | intro n _ ih =>
    exact if hn : P n then ⟨n, hn⟩ else ih (n + 1) ⟨rfl, hn⟩

theorem acc_search_of_exists {P : Nat → Prop} (h : ∃ k, P k) : Acc (Search P) 0 := by
  have ⟨k, hk⟩ := h
  suffices ∀ d n, n + d = k → Acc (Search P) n from this k 0 (Nat.zero_add k)
  intro d
  induction d with
  | zero => rintro n rfl; exact ⟨_, fun _ h => (h.2 hk).elim⟩
  | succ d ih =>
    intro n hn
    exact ⟨_, fun m h => h.1 ▸ ih (n + 1) (by omega)⟩

/-- info: 'PSet.con_ZF_of_dns' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZF_of_dns
