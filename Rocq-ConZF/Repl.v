Require Import Mat.
(*
Replacement for functional relations with values in a class that has uniformly defined
coherent assignments. No totality, no choice: the image is obtained from the value of the
materializing recursion at the root of a tree glued from the assignments of the values.
*)

Section S.
Context {D : PSet -> PSet}.

Section glue.
Variable (T : PSet -> Path -> PSet -> Prop) (s : PSet)
  (φ : PSet -> PSet -> Prop).

(*- The glued assignment: below the child `c x` of the root, the assignment of the value of
`φ` at `x`. The root itself has no target; its value is what we want to construct. *)
Definition Glue (q : Path) (t : PSet) : Prop :=
  exists r x η, q = r ++ (c x::nil) /\ x ∈ s /\ φ x η /\ T η r t.

Lemma append_inj' {s₁ s₂:Path}{a a'} (h : s₁ ++ a :: nil = s₂ ++ a' :: nil) : s₁ = s₂ /\ a = a'.
revert s₂ h; induction s₁.
*intros; destruct s₂ as [|?[|??]]; try discriminate.
 injection h; auto.
*intros.
 destruct s₂ as [|d s₂]; [destruct s₁; discriminate|].
 injection h; clear h; intros.
 subst d.
 apply IHs₁ in H.
 destruct H; subst; auto.
Qed.

Context (*{T s φ}*) {C : PSet -> Prop}
  (hT : forall η, C η -> Coherent D s (T η) /\ T η nil η)
  (hTresp : forall {η η' p t}, η ≈ η' -> T η p t -> T η' p t)
  (φ_resp : forall {x x' y y'}, x ≈ x' -> y ≈ y' -> φ x y -> φ x' y')
  (φ_func : forall {x y y'}, x ∈ s -> φ x y -> φ x y' -> y ≈ y')
  (φ_C : forall {x y}, x ∈ s -> φ x y -> C y).
(*Hint Resolve hTresp φ_func : core.*)

Lemma glue_iff {r x η t} (hx : x ∈ s) (hη : φ x η) : Glue (r ++ c x::nil) t <-> T η r t.
split.
*intros (r' & x' & η' & e & hx' & hη'& h).
 apply append_inj' in e; destruct e as (e1, e2).
 injection e2; intros.
 subst x' r'.
 revert h; apply hTresp.
revert hη' hη; apply φ_func; trivial.
*intros h; exists r; exists x; exists η; split; [|split;[|split]]; trivial.
Qed.

(*include hT φ_resp φ_C*)

Instance glue_coherent : Coherent D s Glue.
split.
*(*resp*)
 intros ? t t' (r& x& η& rfl& hx& hη& h) e.
 exists r; exists x; exists η; split; [|split;[|split]]; trivial.
 revert h e; apply (@resp D s).
 apply hT; apply φ_C with (2:=hη); trivial.
*(*func*)
 intros ? t t' (r & x& η& rfl& hx& hη& h) h'.
 subst p.
 eapply func with (2:=h); [apply hT;apply φ_C with (2:=hη); trivial|].
 rewrite glue_iff with (2:=hη) in h'; trivial.
*(*lab*)
 intros l l' p t e (r& x& η& eq& hx& hη& h).
 destruct r as [|l0 r].
 +injection eq; clear eq; intros; subst l p.
  inversion_clear e.
  exists nil; exists x'; exists η; split;[|split;[|split]]; trivial.
  ++revert hx; apply mem_congr_left; apply Equiv_symm; trivial.
  ++revert hη; apply φ_resp; [trivial|apply Equiv_refl].
 +injection eq; clear eq; intros; subst l0 p.
  exists (l' :: r); exists x; exists η; split;[|split;[|split]]; trivial.
  revert h; eapply lab; [apply hT;apply φ_C with (2:=hη); trivial|];trivial.
*(*desc*)
 intros l ? t t' h (r& x& η& rfl& hx& hη& h').
 subst p.
 eapply @glue_iff with (r:=l::r) (2:=hη) in h; trivial.
 eapply desc with (2:=h); [apply hT;apply φ_C with (2:=hη); trivial|];trivial.
*(*sup*)
 intros ? t G (r& x& η& rfl& hx& hη& h) hG y.
 subst p.
 assert (hG' : IsG (T η) r G).
 {intros z.
  rewrite (hG z).
  apply ex_morph; intros ζ.
  apply and_iff_morphism; [|reflexivity].
  apply @glue_iff with (r := a :: r) (2:=hη); trivial. }
 rewrite sup with (3:=hG'); [|apply hT;apply φ_C with (2:=hη)|];trivial.
 apply ex_morph; intros l.
 apply ex_morph; intros t'.
 apply and_iff_morphism; [reflexivity|].
 apply and_iff_morphism; [|reflexivity].
 symmetry; eapply @glue_iff with (r := l :: r); trivial.
Qed.

(*- The union of the successors of the values of `φ` on `s` exists. The witness is the value
of the recursion at the root. *)
Lemma exists_sup : exists θ : PSet, forall y, y ∈ θ <-> exists x η, x ∈ s /\ φ x η /\ y ∈ succ η.
assert (coh := glue_coherent).
assert (children : forall c, Rel Glue c nil -> forall tc, Glue c tc ->
      Acc (Rel Glue) c /\ forall acc', F D s (Rel Glue) c acc' ≈ tc).
{intros c ? tc htc.
 apply materialize with (1:=glue_coherent); trivial. }
assert (acc : Acc (Rel Glue) nil).
{constructor; intros c h.
 generalize h; intros (? & _ & tc & htc).
 eapply children; eassumption. }
exists (F D s (Rel Glue) nil acc).
intros y.
rewrite F_eq, mem_step_iff; trivial.
*split.
 +intros (l& t'& ?& (r& x& η& eq& hx& hη& h)& hy).
  destruct hT with η as (hc,ht); [apply φ_C with x; trivial|].
  exists x; exists η; split;[|split]; trivial.
  revert hy; apply mem_succ_congr.
  destruct r as [|?[|??]]; try discriminate.
  revert h; eapply func; eauto.
 +intros (x& η& hx& hη& hy).
  exists (c x); exists  η; split; [|split]; trivial.
  ++right; right; exists x; split; [trivial|constructor;apply Equiv_refl].
  ++exists nil; exists x; exists η; split; [|split;[|split]]; trivial.
    destruct hT with η as (hc,ht); [apply φ_C with x; trivial|trivial].
*intros c h tc htc.
 apply children; trivial.
Qed.

(*- **Replacement** for `φ` on `s`, provided the values of `φ` lie in a class `C` every member
`η` of which is the root target of a coherent assignment `T η` given uniformly in `η`. *)
Lemma replacement : exists img : PSet, forall y, y ∈ img <-> exists x, x ∈ s /\ φ x y.
destruct exists_sup as (θ, hθ).
exists (sep (fun y => exists x, x ∈ s /\ φ x y) θ).
intros y.
rewrite mem_sep.
*split; [destruct 1; trivial|].
 intros h; split;[|trivial].
 rewrite hθ.
 destruct h as (x & hx & h).
 exists x; exists y; split;[|split]; trivial.
 apply mem_succ; right; apply Equiv_refl.
*intros z z' e (x & hx & h); exists x; split; trivial.
 revert h; apply φ_resp; [apply Equiv_refl|trivial].
Qed.

End glue.
End S.

Print Assumptions materialize.
Print Assumptions replacement.
