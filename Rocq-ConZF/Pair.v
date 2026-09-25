Require Export PSet.
(*! Kuratowski pairs, used to decode the labels of the definability rule. *)

Definition upair (a b : PSet) : PSet := union (singleton a) (singleton b).

Lemma mem_upair {a b x : PSet} : x ∈ upair a b <-> x ≈ a \/ x ≈ b.
Admitted. (*  mem_union.trans (or_congr mem_singleton mem_singleton).*)

Lemma upair_congr {a a' b b' : PSet} (ha : a ≈ a') (hb : b ≈ b') : upair a b ≈ upair a' b'.
Admitted.
(*ext fun _ => mem_upair.trans <| .trans
    (or_congr ⟨fun e => e.trans ha, fun e => e.trans ha.symm⟩
      ⟨fun e => e.trans hb, fun e => e.trans hb.symm⟩) mem_upair.symm*)

Lemma singleton_congr {a a' : PSet} (h : a ≈ a') : singleton a ≈ singleton a'.
Admitted.
(*ext fun _ => mem_singleton.trans <| .trans
    ⟨fun e => e.trans h, fun e => e.trans h.symm⟩ mem_singleton.symm*)

Definition pair (a b : PSet) : PSet := upair (singleton a) (upair a b).

Lemma pair_congr {a a' b b' : PSet} (ha : a ≈ a') (hb : b ≈ b') : pair a b ≈ pair a' b'.
Admitted.
(*upair_congr (singleton_congr ha) (upair_congr ha hb)*)

Lemma self_mem_singleton (a : PSet) : a ∈ singleton a.
  apply mem_singleton; apply Equiv_refl.
Qed.

(*- `{a} ≈ {c, d}` gives `a ≈ c`. *)
Lemma singleton_eq_upair {a c d : PSet} (h : singleton a ≈ upair c d) : c ≈ a /\ d ≈ a.
Admitted.
  (*  ⟨mem_singleton.1 ((mem_congr_right h).2 (mem_upair.2 (.inl (Equiv.refl _)))),
   mem_singleton.1 ((mem_congr_right h).2 (mem_upair.2 (.inr (Equiv.refl _))))⟩*)

Lemma pair_inj {a b c d : PSet} (h : pair a b ≈ pair c d) : a ≈ c /\ b ≈ d.
Admitted.
(*  have h1 : singleton a ∈ pair c d := (mem_congr_right h).1 (mem_upair.2 (.inl (Equiv.refl _)))
  have hac : a ≈ c := by
    rcases mem_upair.1 h1 with e | e
    · exact mem_singleton.1 ((mem_congr_right e).1 (self_mem_singleton a))
    · exact (singleton_eq_upair e).1.symm
  refine ⟨hac, ?_⟩
  have h2 : upair a b ∈ pair c d := (mem_congr_right h).1 (mem_upair.2 (.inr (Equiv.refl _)))
  have h3 : upair c d ∈ pair a b := (mem_congr_right h).2 (mem_upair.2 (.inr (Equiv.refl _)))
  have hb : b ∈ upair a b := mem_upair.2 (.inr (Equiv.refl _))
  have hd : d ∈ upair c d := mem_upair.2 (.inr (Equiv.refl _))
  rcases mem_upair.1 h2 with e | e
  · -- `{a, b} ≈ {c}`: then `b ≈ c ≈ a`, and `d` is `a` or `b`
    have hbc : b ≈ c := mem_singleton.1 ((mem_congr_right e).1 hb)
    rcases mem_upair.1 h3 with e' | e'
    · exact hbc.trans (hac.symm.trans (mem_singleton.1 ((mem_congr_right e').1 hd)).symm)
    · rcases mem_upair.1 ((mem_congr_right e').1 hd) with e'' | e''
      · exact hbc.trans (hac.symm.trans e''.symm)
      · exact e''.symm
  · rcases mem_upair.1 ((mem_congr_right e).1 hb) with e' | e'
    · -- `b ≈ c`: `d ∈ {a, b}` gives `d ≈ a ≈ c ≈ b` or `d ≈ b`
      rcases mem_upair.1 ((mem_congr_right e).2 hd) with e'' | e''
      · exact e'.trans (hac.symm.trans e''.symm)
      · exact e''.symm
    · exact e'*)

(*- Triples, as nested pairs. *)
Definition triple (a b c : PSet) : PSet := pair a (pair b c).

Lemma triple_congr {a a' b b' c c' : PSet} (ha : a ≈ a') (hb : b ≈ b') (hc : c ≈ c') :
  triple a b c ≈ triple a' b' c'.
  apply pair_congr; [trivial|apply pair_congr; trivial].
Qed.

Lemma triple_inj {a b c a' b' c' : PSet} (h : triple a b c ≈ triple a' b' c') :
  a ≈ a' /\ b ≈ b' /\ c ≈ c'.
  apply pair_inj in h; destruct h as (?,h).
  apply pair_inj in h; destruct h; auto.
Qed.

