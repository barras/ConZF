Require Import Ord Pair.
(*!
Power set, the levels `V_x` (for any set `x`, of rank `rank x`), finite ordinals and `ω`, and the
label set `D G = V_{G+ω}` of the definability rule, all characterized through ranks.
*)

Import PSet.

(*- Power set: subsets are indexed by predicates on the index type, which is small because
`Prop` is impredicative. *)
Definition powerset (X : PSet) : PSet :=
  range (ι := Idx X -> Prop) (fun S => range (ι := {i | S i}) (fun i => Func X (proj1_sig i))).

Lemma mem_powerset {X y : PSet} : y ∈ powerset X <-> forall z, z ∈ y -> z ∈ X.
Admitted.
(*  refine ⟨fun ⟨S, e⟩ z hz => ?_, fun h => ⟨fun i => X.Func i ∈ y, ext fun z => ⟨fun hz => ?_, ?_⟩⟩⟩
  · have ⟨⟨i, _⟩, e'⟩ := (mem_congr_right e).1 hz
    exact ⟨i, e'⟩
  · have ⟨i, e'⟩ := h z hz
    exact ⟨⟨i, (mem_congr_left e').1 hz⟩, e'⟩
  · rintro ⟨⟨i, hi⟩, e'⟩
    exact (mem_congr_left e').2 hi*)

(*- `z ∈ rank x` iff `z ≤ rank y` for some `y ∈ x`. *)
Lemma mem_rank' {x z : PSet} : z ∈ rank x <-> exists y, y ∈ x /\ z ∈ succ (rank y).
Admitted.
(*mem_rank_trans ⟨fun ⟨a, h⟩ => ⟨_, func_mem x a, h⟩,
    fun ⟨_, ⟨a, e⟩, h⟩ => ⟨a, (mem_succ_congr (rank_congr e)).1 h⟩⟩*)

Lemma succ_congr {a a' : PSet} (h : a ≈ a') : succ a ≈ succ a'.
Admitted.
(*ext fun _ => mem_succ_congr h*)

(*- The rank of an ordinal is itself. *)
Lemma IsOrd_rank_equiv : forall {t : PSet}, IsOrd t -> rank t ≈ t.
Admitted.
(*intro t
  induction t using mem_induction with | _ t ih => ?_
  intro ht
  refine ext fun z => mem_rank'.trans ⟨fun ⟨y, hy, hz⟩ => ?_, fun hz => ⟨z, hz, ?_⟩⟩
  · rcases mem_succ.1 ((mem_succ_congr (ih y hy (ht.mem hy))).1 hz) with hz | e
    · exact ht.trans y hy z hz
    · exact (mem_congr_left e).2 hy
  · exact (mem_succ_congr (ih z hz (ht.mem hz))).2 (mem_succ.2 (.inr (Equiv.refl _)))*)

Section em.
Hypothesis (em : forall p : Prop, p \/ ~p).

(*- If every element of `y` has rank below the ordinal `R`, then `rank y ≤ R`. *)
Lemma rank_mem_succ {y R : PSet} (hR : IsOrd R) (h : forall z, z ∈ y -> rank z ∈ R) :
    rank y ∈ succ R.
Proof using em.
Admitted.
(*refine mem_succ.2 ((isOrd_rank y).subset em hR fun w hw => ?_)
  have ⟨z, hz, hw⟩ := mem_rank'.1 hw
  rcases mem_succ.1 hw with hw | e
  · exact hR.trans _ (h z hz) w hw
  · exact (mem_congr_left e).2 (h z hz)*)

Lemma rank_singleton_mem {a R : PSet} (hR : IsOrd R) (ha : rank a ∈ R) :
    rank (singleton a) ∈ succ R.
Admitted.
(*rank_mem_succ em hR fun _ hz => (mem_congr_left (rank_congr (mem_singleton.1 hz))).2 ha*)

Lemma rank_upair_mem {a b R : PSet} (hR : IsOrd R) (ha : rank a ∈ R) (hb : rank b ∈ R) :
    rank (upair a b) ∈ succ R.
Admitted.
(*rank_mem_succ em hR fun _ hz => (mem_upair.1 hz).elim
    (fun e => (mem_congr_left (rank_congr e)).2 ha) (fun e => (mem_congr_left (rank_congr e)).2 hb)*)

Lemma rank_pair_mem {a b R : PSet} (hR : IsOrd R) (ha : rank a ∈ R) (hb : rank b ∈ R) :
    rank (pair a b) ∈ succ (succ R).
Admitted.
(*rank_upair_mem em hR.succ (rank_singleton_mem em hR ha) (rank_upair_mem em hR ha hb)*)

Lemma rank_triple_mem {a b c R : PSet} (hR : IsOrd R)
    (ha : rank a ∈ R) (hb : rank b ∈ R) (hc : rank c ∈ R) :
    rank (triple a b c) ∈ succ (succ (succ (succ R))).
Admitted.
(*rank_pair_mem em hR.succ.succ
    (mem_succ.2 (.inl (mem_succ.2 (.inl ha)))) (rank_pair_mem em hR hb hc)*)

End em.

(*! ### Levels *)

(*- `Vl x` is the set of sets of rank below `rank x`. *)
Fixpoint Vl (x:PSet) : PSet :=
  iUnion (fun a => powerset (Vl (Func x a))).

Lemma mem_Vl (em : forall p : Prop, p \/ ~p) : forall {x y : PSet}, y ∈ Vl x <-> rank y ∈ rank x.
Admitted.
(*| ⟨_, A⟩, y => by
    refine mem_iUnion.trans <| .trans ?_ mem_rank.symm
    refine exists_congr fun a => mem_powerset.trans ⟨fun h => ?_, fun h z hz => ?_⟩
    · exact rank_mem_succ em (isOrd_rank _) fun z hz => (mem_Vl em).1 (h z hz)
    · refine (mem_Vl em).2 ?_
      have hz' := rank_mem hz
      rcases mem_succ.1 h with h | e
      · exact (isOrd_rank _).trans _ h _ hz'
      · exact (mem_congr_right e).1 hz'*)

(*! ### Finite ordinals and `ω` *)

Fixpoint ofNat (n : nat) : PSet :=
  match n with
  | 0 => empty
  | S n => succ (ofNat n)
  end.

Lemma isOrd_ofNat : forall n, IsOrd (ofNat n).
  induction n; [apply isOrd_empty|simpl;apply IsOrd_succ; trivial].  
Qed.

Definition omega : PSet :=
  range (ι := nat) (fun n => ofNat n).

Lemma mem_omega {x : PSet} : x ∈ omega <-> exists n, x ≈ ofNat n.
Admitted.
(*  ⟨fun ⟨n, e⟩ => ⟨n.down, e⟩, fun ⟨n, e⟩ => ⟨⟨n⟩, e⟩⟩*)

Lemma isOrd_omega : IsOrd omega.
Admitted.
(*refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · have ⟨n, e⟩ := mem_omega.1 hy
    induction n generalizing y z with
    | zero => exact ((not_mem_empty z) ((mem_congr_right e).1 hz)).elim
    | succ n ih =>
      rcases mem_succ.1 ((mem_congr_right e).1 hz) with h | e'
      · exact ih _ (mem_omega.2 ⟨n, Equiv.refl _⟩) _ h (Equiv.refl _)
      · exact mem_omega.2 ⟨n, e'⟩
  · have ⟨n, e⟩ := mem_omega.1 hy
    exact ((isOrd_ofNat n).resp e.symm).trans*)

(*! ### The label set *)

Fixpoint succN (n:nat) (G:PSet) : PSet :=
  match n with
  | 0 => G
  | S n => succ (succN n G)
  end.

(*- `D G = V_{rank G + ω}`. *)
Definition D (G : PSet) : PSet :=
  iUnion (ι := nat) (fun n => Vl (succN n G)).

Lemma mem_D (em : forall p : Prop, p \/ ~p) {G y : PSet} :
    y ∈ D G <-> exists n, rank y ∈ rank (succN n G).
Admitted.
(*mem_iUnion.trans ⟨fun ⟨n, h⟩ => ⟨n.down, (mem_Vl em).1 h⟩, fun ⟨n, h⟩ => ⟨⟨n⟩, (mem_Vl em).2 h⟩⟩*)

Lemma IsOrd_iterate_succ {G : PSet} (h : IsOrd G) : forall n, IsOrd (succN n G).
Admitted.
(*| 0 => h
  | n+1 => (h.iterate_succ n).succ*)

(*- For an ordinal `G`, a set whose rank is below `G + n` is in `D G`. *)
Lemma mem_D_of_rank (em : forall p : Prop, p \/ ~p) {G y : PSet} (hG : IsOrd G) (n : nat)
    (h : rank y ∈ succN n G) : y ∈ D G.
Admitted.
(*(mem_D em).2 ⟨n, (mem_congr_right (hG.iterate_succ n).rank_equiv).2 h⟩*)
