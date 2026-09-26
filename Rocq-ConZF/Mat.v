Require Export PSet.
From Stdlib Require Export List.
(*
The materializing recursion (doc/main.tex, section 3). Paths are lists of labels, a type in
the same universe as `PSet`; targets are arbitrary sets; and the operation `D` (in the
application: `G ↦ V_{rank G + ω}`) is an arbitrary parameter.
*)

(*- Labels of children: the child `a`, whose value `G` is computed first; the children
`b w` for `w ∈ D G`; and the children `c x` for `x` in a parameter set. *)
Inductive Label : Type :=
  | a
  | b (w : PSet)
  | c (x : PSet).

Inductive Label_Equiv : Label -> Label -> Prop :=
  | aEq : Label_Equiv a a
  | bEq {w w'} : w ≈ w' -> Label_Equiv (b w) (b w')
  | cEq {x x'} : x ≈ x' -> Label_Equiv (c x) (c x').

(*- A path, deepest label first. The carrier of the recursion; it lives in `Type (u+1)`,
the same universe as `PSet`. *)
Notation Path := (list Label).
(*Abbreviation Path := (list Label).*)

Section S.
Variable (D : PSet -> PSet) (U : PSet).

Section step.

  Variable (R : Path -> Path -> Prop) (p : Path)
  (rec : forall (c : Path), R c p -> PSet).

(*- A guarded recursive call: `succ (rec (l :: p))` if `l :: p` is below `p`, else `∅`. *)
Definition call (l : Label) : PSet :=
  guard (R (l :: p) p) (fun h => succ (rec (l :: p) h)).

(*- The value of the first call, or `∅`. *)
Definition stepG : PSet :=
  guard (R (a :: p) p) (fun h => rec (a :: p) h).

(*- The step of the recursion. The second family of calls is indexed by the index type of
`D G`, where `G` is the value of the first call. *)
Definition step : PSet :=
  union (call a)
    (union
       (iUnion (fun i : Idx (D stepG) => call (b (Func (D stepG) i))))
       (iUnion (fun j : Idx U => call (c (Func U j))))).

End step.

(*- The materializing recursion: `Acc`-recursion on the big carrier `Path`, with motive
the big type `PSet`. *)
Definition F (R : Path -> Path -> Prop) (p : Path) (acc : Acc R p) : PSet :=
  Acc_rect (fun _ => PSet)
    (fun p _ ih => step R p ih) acc.

Lemma F_eq R (p : Path) (acc : Acc R p) :
  F R p acc = step R p (fun c h => F R c (Acc_inv acc h)).
destruct acc; reflexivity.
Qed.

(*! ### Target assignments *)

(*- The relation of a target assignment: `c` is a child of `p` and has a target. *)
Definition Rel (τ : Path -> PSet -> Prop) (c p : Path) : Prop :=
  exists l, c = l :: p /\ exists t, τ c t.

(*- `G` is the target of the child `a` of `p`, or empty if there is none. *)
Definition IsG (τ : Path -> PSet -> Prop) (p : Path) (G : PSet) : Prop :=
  forall x, x ∈ G <-> exists ζ, τ (a :: p) ζ /\ x ∈ ζ.

(*- The labels the step enumerates when the first call returns `G`. *)
Definition Avail (G : PSet) (l : Label) : Prop :=
  l = a \/
    (exists w, w ∈ D G /\ Label_Equiv l (b w)) \/ exists x, x ∈ U /\ Label_Equiv l (c x).

(*- A coherent target assignment. It is a proposition about a relation; no part of it is
data. *)
Class Coherent (τ : Path -> PSet -> Prop) : Prop := {
  (*- targets are determined up to bisimulation *)
  resp : forall {p t t'}, τ p t -> t ≈ t' -> τ p t';
  func : forall {p t t'}, τ p t -> τ p t' -> t ≈ t';
  (*- the assignment does not see the representation of a label *)
  lab : forall {l l' p t}, Label_Equiv l l' -> τ (l :: p) t -> τ (l' :: p) t;
  (*- the target of a child is an element of the target of its parent *)
  desc : forall {l p t t'}, τ (l :: p) t -> τ p t' -> t ∈ t';
  (*- a target is the union of the successors of the targets of the available children *)
  sup : forall {p t G}, τ p t -> IsG τ p G ->
                        forall x, x ∈ t <-> exists l t', Avail G l /\ τ (l :: p) t' /\ x ∈ succ t'
  }.


(*variable {D U}*)

(*- What the step computes, given that the recursive calls return the targets. *)
Lemma mem_step_iff {τ : Path -> PSet -> Prop} (hτ : Coherent τ) {p : Path}
    {rec : forall (c : Path), Rel τ c p -> PSet}
    (hrec : forall c h t, τ c t -> rec c h ≈ t) (x : PSet) :
    x ∈ step (Rel τ) p rec <->
      exists l t', Avail (stepG (Rel τ) p rec) l /\ τ (l :: p) t' /\ x ∈ succ t'.
assert(hcall : forall l, x ∈ call (Rel τ) p rec l <-> exists t', τ (l :: p) t' /\ x ∈ succ t').
{intros l.
 unfold call; rewrite mem_guard.
 split.
 *intros (h, hx).
  destruct (h) as (?&?& t'& ht').
  exists t'; split; [trivial|].
  revert hx; apply mem_succ_congr.
  apply Equiv_symm; apply hrec; trivial.
 *intros (t' & ht' & hx).
  assert (h : Rel τ (l :: p) p) by (exists l; eauto).
  exists h.
  revert hx; apply mem_succ_congr.
  apply hrec; trivial. }
unfold step; rewrite mem_union.
rewrite mem_union.
rewrite !mem_iUnion.
split.
*intros [h | [(i, h)|(j, h)]]; apply hcall in h; destruct h as (t'& h1& h2).
 +exists a; exists t'; split;[|split]; trivial.
  left; trivial.
 +eexists; exists t'; split;[right;left|split]; try eassumption.
  eexists; split; [|constructor;apply Equiv_refl].
  apply func_mem.
 +eexists; exists t'; split;[right;right|split]; try eassumption.
  eexists; split; [|constructor;apply Equiv_refl].
  apply func_mem.
*intros (l & t' & [hl |[(w & (i, e)& hl) | (y& (j, e) & hl)]]& h1& h2).
 +subst l; left; apply hcall; exists t'; auto.
 +right; left; exists i; apply hcall.
  exists t'; split; trivial.
  revert h1; inversion_clear hl.
  apply lab; constructor.
  apply Equiv_trans with (2:=e); trivial.
 +right; right;exists j; apply hcall.
  exists t'; split; trivial.
  revert h1; inversion_clear hl.
  apply lab; constructor.
  apply Equiv_trans with (2:=e); trivial.
Qed.

Lemma isG_stepG {τ : Path -> PSet -> Prop} {p : Path}
    {rec : forall (c : Path), Rel τ c p -> PSet}
    (hrec : forall c h t, τ c t -> rec c h ≈ t) :
  IsG τ p (stepG (Rel τ) p rec).
intros x.
unfold stepG; rewrite mem_guard.
split.
*intros (h, hx).
 destruct (h) as (?&?& ζ& hζ).
 exists ζ; split; [trivial|].
 revert hx; apply mem_congr_right.
 apply Equiv_symm; apply hrec; trivial.
*intros (ζ& hζ& hx).
 assert (h : Rel τ (a :: p) p) by (exists a; eauto).
 exists h.
 revert hx; apply mem_congr_right.
 apply hrec; trivial.
Qed.

(*- **Materialization.** If `τ` is coherent and `p` has the target `t`, then `p` is accessible
and the recursion returns `t`: a set specified by a proposition is the value of a term. *)
Lemma materialize {τ : Path -> PSet -> Prop} (hτ : Coherent τ) :
    forall (t : PSet) (p : Path), τ p t ->
    Acc (Rel τ) p /\ forall acc', F (Rel τ) p acc' ≈ t.
induction t using @mem_induction.
intros p hp.
assert (children : forall c, Rel τ c p -> forall tc, τ c tc ->
      Acc (Rel τ) c /\ forall acc', F (Rel τ) c acc' ≈ tc).
{intros c (l & rfl & ?) tc htc.
 subst c.
 apply H; trivial.
 apply desc with (1:=htc); trivial. }
assert (acc : Acc (Rel τ) p).
{constructor.
 intros c h.
 destruct (h) as (?&?& tc& htc).
 eapply children with (2:=htc); trivial. }
split; [trivial|].
intros acc'; apply ext; intros x.
rewrite F_eq.
assert (hrec : forall c (h : Rel τ c p) tc, τ c tc -> F (Rel τ) c (Acc_inv acc' h) ≈ tc).
{intros c h tc htc; apply children with (2:=htc); trivial. }
rewrite mem_step_iff; trivial.
symmetry; apply sup; trivial.
apply isG_stepG; trivial.
Qed.

End S.
