Require Export PSet.
(*! Kuratowski pairs, used to decode the labels of the definability rule. *)

Definition upair (a b : PSet) : PSet := union (singleton a) (singleton b).

Lemma mem_upair {a b x : PSet} : x ∈ upair a b <-> x ≈ a \/ x ≈ b.
unfold upair; rewrite mem_union, !mem_singleton; reflexivity.
Qed.

Lemma upair_congr {a a' b b' : PSet} (ha : a ≈ a') (hb : b ≈ b') : upair a b ≈ upair a' b'.
apply ext; intros z.
rewrite !mem_upair.
apply or_iff_morphism;
  split; eauto using Equiv_trans, Equiv_symm.
Qed.

Lemma singleton_congr {a a' : PSet} (h : a ≈ a') : singleton a ≈ singleton a'.
apply ext; intros z.
rewrite !mem_singleton;
  split; eauto using Equiv_trans, Equiv_symm.
Qed.

Definition pair (a b : PSet) : PSet := upair (singleton a) (upair a b).

Lemma pair_congr {a a' b b' : PSet} (ha : a ≈ a') (hb : b ≈ b') : pair a b ≈ pair a' b'.
apply upair_congr; [apply singleton_congr|apply upair_congr]; trivial.
Qed.

Lemma self_mem_singleton (a : PSet) : a ∈ singleton a.
  apply mem_singleton; apply Equiv_refl.
Qed.

(*- `{a} ≈ {c, d}` gives `a ≈ c`. *)
Lemma singleton_eq_upair {a c d : PSet} (h : singleton a ≈ upair c d) : c ≈ a /\ d ≈ a.
split.
*apply mem_singleton.
 apply mem_congr_right with (1:=h).
 apply mem_upair; left; apply Equiv_refl.
*apply mem_singleton.
 apply mem_congr_right with (1:=h).
 apply mem_upair; right; apply Equiv_refl.
Qed.

Lemma pair_inj {a b c d : PSet} (h : pair a b ≈ pair c d) : a ≈ c /\ b ≈ d.
assert (h1 : singleton a ∈ pair c d).
{apply mem_congr_right with (1:=h).
 apply mem_upair; left; apply Equiv_refl. }
assert (hac : a ≈ c).
{apply mem_upair in h1; destruct h1.
 *apply mem_singleton.
  apply mem_congr_right with (1:=H).
  apply mem_singleton; apply Equiv_refl.
 *apply singleton_eq_upair in H.
  apply Equiv_symm; apply H. }
split; [trivial|].
assert (h2 : upair a b ∈ pair c d).
{apply mem_congr_right  with (1:=h).
 apply mem_upair; right; apply Equiv_refl. }
assert (h3 : upair c d ∈ pair a b).
{apply mem_congr_right  with (1:=h).
 apply mem_upair; right; apply Equiv_refl. }
assert (hb : b ∈ upair a b).
{apply mem_upair; right; apply Equiv_refl. }
assert (hd : d ∈ upair c d).
{apply mem_upair; right; apply Equiv_refl. }
apply mem_upair in h2; destruct h2 as [e|e].
*(*-- `{a, b} ≈ {c}`: then `b ≈ c ≈ a`, and `d` is `a` or `b`*)
  assert (hbc : b ≈ c).
  {apply mem_singleton.
   apply mem_congr_right with (1:=e); trivial. }
  apply mem_upair in h3; destruct h3 as [e' | e'].
  **apply Equiv_trans with (1:=hbc).
    apply Equiv_trans with (1:=Equiv_symm hac).
    apply Equiv_symm.
    apply mem_singleton.
    apply mem_congr_right with (1:=e'); trivial.
  **apply mem_congr_right with (1:=e') in hd.
    apply mem_upair in hd; destruct hd as [e''|e''];
      eauto using Equiv_trans, Equiv_symm.
*apply mem_congr_right with (1:=e) in hb.
 apply mem_upair in hb; destruct hb as [e' | e'].
 **(* -- `b ≈ c`: `d ∈ {a, b}` gives `d ≈ a ≈ c ≈ b` or `d ≈ b`*)
   apply mem_congr_right with (1:=e) in hd.
   apply mem_upair in hd; destruct hd as [e'' | e''];
      eauto using Equiv_trans, Equiv_symm.
 **trivial.
Qed.

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

