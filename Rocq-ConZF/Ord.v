Require Import Repl.
(*import ConZF.NatInstance*)
(*!
Ordinals and rank. Excluded middle, where needed, is an explicit hypothesis
`em : forall p : Prop, p \/ ¬p`, never `Classical.em` (which is proved from choice).
*)
Import PSet.

Definition Trans (t : PSet) : Prop := forall y, y ∈ t -> forall z, z ∈ y -> z ∈ t.

(*- Von Neumann ordinals: transitive sets of transitive sets (foundation is built in). *)
Class IsOrd (t : PSet) : Prop := {
    IsOrd_trans : Trans t;
    IsOrd_mem_trans : forall y, y ∈ t -> Trans y
  }.

Lemma Trans_resp {t t' : PSet} (e : t ≈ t') (h : Trans t) : Trans t'.
Admitted.
(*  fun y hy z hz => (mem_congr_right e).1 (h y ((mem_congr_right e).2 hy) z hz)*)

Lemma IsOrd_resp {t t' : PSet} (e : t ≈ t') (h : IsOrd t) : IsOrd t'.
Admitted.
(*⟨h.trans.resp e, fun y hy => h.mem_trans y ((mem_congr_right e).2 hy)⟩*)

Lemma IsOrd_mem {t y : PSet} (h : IsOrd t) (hy : y ∈ t) : IsOrd y.
Admitted.
(*  ⟨h.mem_trans y hy, fun z hz => h.mem_trans z (h.trans y hy z hz)⟩*)

Lemma isOrd_empty : IsOrd empty.
Admitted.
(*⟨fun _ h => (not_mem_empty _ h).elim, fun _ h => (not_mem_empty _ h).elim⟩*)

Instance IsOrd_succ {t : PSet} (h : IsOrd t) : IsOrd (succ t).
Admitted.
(*refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · rcases mem_succ.1 hy with hy | e
    · exact mem_succ.2 (.inl (h.trans y hy z hz))
    · exact mem_succ.2 (.inl ((mem_congr_right e).1 hz))
  · rcases mem_succ.1 hy with hy | e
    · exact h.mem_trans y hy
    · exact h.trans.resp e.symm*)

Instance isOrd_iUnion {ι : Type} {A : ι -> PSet} (h : forall i, IsOrd (A i)) : IsOrd (iUnion A).
Admitted.
(*refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · have ⟨i, hi⟩ := mem_iUnion.1 hy
    exact mem_iUnion.2 ⟨i, (h i).trans y hi z hz⟩
  · have ⟨i, hi⟩ := mem_iUnion.1 hy
    exact (h i).mem_trans y hi*)

Lemma not_mem_self (a : PSet) : ~ a ∈ a.
Admitted.
(*  := fun h => mem_asymm a h h*)

Section em.
Hypothesis (em : forall p : Prop, p \/ ~p).

(*- Ordinals are linearly ordered by `∈`. *)
Lemma IsOrd_trichotomy : forall {a b : PSet}, IsOrd a -> IsOrd b -> a ∈ b \/ a ≈ b \/ b ∈ a.
Proof using em.
Admitted.
(*  intro a
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
    · exact h*)

(*- For ordinals, inclusion is `∈` or `≈`. *)
Lemma IsOrd_subset {a b : PSet} (ha : IsOrd a) (hb : IsOrd b) (h : forall z, z ∈ a -> z ∈ b) :
  a ∈ b \/ a ≈ b.
Proof using em.
Admitted.
(*  rcases ha.trichotomy em hb with h' | h' | h'
  · exact .inl h'
  · exact .inr h'
  · exact (not_mem_self b (h b h')).elim*)

End em.

(*! ### Rank *)

Fixpoint rank (x:PSet) : PSet :=
  iUnion (fun a:Idx x => succ (rank (Func x a))).

Lemma mem_rank {x z : PSet} : z ∈ rank x <-> exists a, z ∈ succ (rank (Func x a)).
destruct x; exact mem_iUnion.
Qed.

Lemma rank_congr : forall {x y : PSet}, x ≈ y -> rank x ≈ rank y.
Admitted.
(*| ⟨_, _⟩, ⟨_, _⟩, ⟨h1, h2⟩ => ext fun _ =>
    ⟨fun h => have ⟨a, h⟩ := mem_iUnion.1 h
       have ⟨b, e⟩ := h1 a
       mem_iUnion.2 ⟨b, (mem_succ_congr (rank_congr e)).1 h⟩,
     fun h => have ⟨b, h⟩ := mem_iUnion.1 h
       have ⟨a, e⟩ := h2 b
       mem_iUnion.2 ⟨a, (mem_succ_congr (rank_congr e)).2 h⟩⟩*)

Lemma rank_mem {x y : PSet} (h : y ∈ x) : rank y ∈ rank x.
Admitted.
(*have ⟨a, e⟩ := h
  mem_rank.2 ⟨a, mem_succ.2 (.inr (rank_congr e))⟩*)

Lemma isOrd_rank : forall x : PSet, IsOrd (rank x).
Admitted.
(*| ⟨_, A⟩ => isOrd_iUnion fun a => (isOrd_rank (A a)).succ*)
