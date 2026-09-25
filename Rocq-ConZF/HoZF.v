Require Import PSet Pair VLevel.
(*import ConZF.Proof*)
(*!
`ZF` as a first-order theory: extensionality, foundation, pairing, union, power set, infinity,
and the schemas of separation and replacement. Free variables of an axiom are parameters. The
replacement schema is in its usual form "a functional relation on `a` has its values in some
`b`"; with separation this gives the image.

`ZFModel M` lists closure conditions on a class of sets which make every axiom valid in it.
*)

(*- `forall z (z ∈ x <-> z ∈ y) -> x = y` *)
Definition Ax_ext (x y : PSet) : Prop :=
  (forall z, z ∈ x <-> z ∈ y) -> (x ≈ y).

(*- `existsz z ∈ x -> existsy (y ∈ x /\ forallz (z ∈ y -> z ∉ x))` *)
Definition Ax_found (x:PSet) : Prop :=
  (exists z, z ∈ x) ->
  exists y,  y ∈ x /\ forall z, z ∈ y -> ~ z ∈ x.

(*- `existsz (x ∈ z /\ y ∈ z)` *)
Definition Ax_pair (x y:PSet) : Prop := exists z, x ∈ z /\ y ∈ z.

(*- `existsu forally forallz (z ∈ y -> y ∈ x -> z ∈ u)` *)
Definition Ax_union (x:PSet) : Prop :=
  exists u, forall y z,  z ∈ y -> y ∈ x -> z ∈ u.

(*- `existsp forally (forallz (z ∈ y -> z ∈ x) -> y ∈ p)` *)
Definition Ax_power (x:PSet) : Prop :=
  exists p, forall y, (forall z, z ∈ y -> z ∈ x) -> y ∈ p.

(*- `existsw (existse (e ∈ w /\ forallz z ∉ e) /\ forally (y ∈ w -> existss (s ∈ w /\ forallz (z ∈ s <-> z ∈ y \/ z = y))))` *)
Definition Ax_inf : Prop :=
  exists w,
    (exists e, e ∈ w /\ forall z, ~ z ∈ e) /\
      (forall y, y ∈ w -> exists s, s ∈ w /\ forall z, z ∈ s <-> z ∈ y \/  z ≈ y).

(*- `existsy forallz (z ∈ y <-> z ∈ x /\ ψ(z, params))`, where `ψ` has `z` as variable `0` and the free
variables of the axiom (`x` among them) as its variables `n+1`. *)
Definition Ax_sep (x:PSet) (ψ : PSet -> Prop) : Prop :=
  exists y, forall z, z ∈ y <-> z ∈ x /\ ψ z.

(*- `forallx (x ∈ a -> forally forally' (ψ(x,y) -> ψ(x,y') -> y = y')) -> existsb forally (existsx (x ∈ a /\ ψ(x,y)) -> y ∈ b)`,
where `ψ` has `x`, `y` as variables `0`, `1` and the free variables of the axiom (`a` among
them) as its variables `n+2`. *)
Definition Ax_repl (a:PSet) (ψ : PSet->PSet->Prop) : Prop :=
  (forall x, x ∈ a -> forall y y', ψ x y -> ψ x y' -> y ≈ y') ->
  exists b, forall y, (exists x, x ∈ a /\ ψ x y) -> y ∈ b.


(*- The axioms of `ZF`. *)
Inductive ZF : Prop -> Prop :=
  | V_ext {x y}: ZF (Ax_ext x y)
  | V_found {x}: ZF (Ax_found x)
  | V_pair {x y}: ZF (Ax_pair x y)
  | V_union {x}: ZF (Ax_union x)
  | V_power {x}: ZF (Ax_power x)
  | V_inf : ZF Ax_inf
  | V_sep x (ψ : PSet->Prop) : ZF (Ax_sep x ψ)
  | V_repl x (ψ : PSet->PSet->Prop) : ZF (Ax_repl x ψ).

(*- Closure conditions on a class which make it a model of `ZF`. *)
Class ZFModel (M : PSet -> Prop) : Prop  := {
  Mtrans : forall {x z}, M x -> z ∈ x -> M z;
  Mempty : M empty;
  Mupair : forall {x y}, M x -> M y -> M (upair x y);
  MsUnion : forall {x}, M x -> M (sUnion x);
  Mpowerset : forall {x}, M x -> M (powerset x);
  Momega : M omega;
  Msep : forall (P : PSet -> Prop) {x}, M x -> M (sep P x);
  Mrepl : forall (ψ : PSet->PSet->Prop), (* all free vars of ψ in M... *)
    forall a, M a ->
    (forall x y y', x ∈ a -> M y -> M y' -> ψ x y -> ψ x y' -> y ≈ y') ->
    exists b, M b /\ forall x y, x ∈ a -> M y -> ψ x y -> y ∈ b
  }.

(*- Every nonempty subset of a set has an `∈`-minimal element. *)
Lemma exists_minimal (em : forall p : Prop, p \/ ~p) (x : PSet) :
  forall z, z ∈ x -> exists y, y ∈ x /\ forall w, w ∈ y -> ~ w ∈ x.
Admitted.
(*  intro z
  induction z using ∈_induction with | _ z ih => ?_
  intro hz
  rcases em (exists w, w ∈ z /\ w ∈ x) with ⟨w, hw, hwx⟩ | h
  · exact ih w hw hwx
  · exact ⟨z, hz, fun w hw hwx => h ⟨w, hw, hwx⟩⟩*)

Section ZFModel.
Context {M : PSet -> Prop} (hM : ZFModel M) (em : forall p : Prop, p \/ ~p).

Lemma valid : forall φ, ZF φ -> φ.
Admitted.
(*  := by
  intro φ h e he
  cases h with
  | ext =>
    intro h
    exact ext fun z =>
      ⟨fun hz => ((sat_iff em).1 (h z (hM.trans (he 0) hz))).1 hz,
       fun hz => ((sat_iff em).1 (h z (hM.trans (he 1) hz))).2 hz⟩
  | found =>
    intro h
    have ⟨z, _, hz⟩ := (sat_ex em).1 h
    have ⟨y, hy, hmin⟩ := exists_minimal em (e 0) z hz
    exact (sat_ex em).2 ⟨y, hM.trans (he 0) hy,
      (sat_and em).2 ⟨hy, fun w _ hw hwx => hmin w hw hwx⟩⟩
  | pair =>
    exact (sat_ex em).2 ⟨PSet.upair (e 0) (e 1), hM.upair (he 0) (he 1),
      (sat_and em).2 ⟨∈_upair.2 (.inl (Equiv.refl _)), ∈_upair.2 (.inr (Equiv.refl _))⟩⟩
  | union =>
    exact (sat_ex em).2 ⟨PSet.sUnion (e 0), hM.sUnion (he 0),
      fun y _ z _ hz hy => ∈_sUnion.2 ⟨y, hy, hz⟩⟩
  | power =>
    exact (sat_ex em).2 ⟨PSet.powerset (e 0), hM.powerset (he 0),
      fun y hy h => ∈_powerset.2 fun z hz => h z (hM.trans hy hz) hz⟩
  | inf =>
    refine (sat_ex em).2 ⟨PSet.omega, hM.omega, (sat_and em).2 ⟨?_, fun y _ hy => ?_⟩⟩
    · exact (sat_ex em).2 ⟨PSet.empty, hM.empty,
        (sat_and em).2 ⟨∈_omega.2 ⟨0, Equiv.refl _⟩, fun z _ hz => not_∈_empty z hz⟩⟩
    · have ⟨n, e'⟩ := ∈_omega.1 hy
      refine (sat_ex em).2 ⟨ofNat (n+1), hM.trans hM.omega (∈_omega.2 ⟨n+1, Equiv.refl _⟩),
        (sat_and em).2 ⟨∈_omega.2 ⟨n+1, Equiv.refl _⟩, fun z _ => (sat_iff em).2 ?_⟩⟩
      refine ∈_succ.trans <| .trans ?_ (sat_or em).symm
      exact or_congr (∈_congr_right e').symm ⟨fun h => h.trans e'.symm, fun h => h.trans e'⟩
  | sep ψ =>
    let P : PSet -> Prop := fun z => Sat M ψ (Env.cons z e)
    have hP : forall z z' : PSet, z ≈ z' -> P z -> P z' := fun _ _ ez h =>
      Sat.resp ψ (Env.cons_resp ez fun _ => Equiv.refl _) h
    refine (sat_ex em).2 ⟨PSet.sep P (e 0), hM.sep P (he 0), fun z _ => (sat_iff em).2 ?_⟩
    have hPz : P z <-> Sat M (rename Ax_sepR ψ) (Env.cons z (Env.cons (PSet.sep P (e 0)) e)) :=
      .trans (Sat.resp_iff (fun _ => Iff.rfl) ψ fun i => by cases i <;> exact Equiv.refl _)
        (sat_rename ψ Ax_sepR _).symm
    refine (∈_sep hP).trans ⟨fun ⟨a, b⟩ => (sat_and em).2 ⟨a, hPz.1 b⟩, fun h => ?_⟩
    have ⟨a, b⟩ := (sat_and em).1 h
    exact ⟨a, hPz.2 b⟩
  | repl ψ =>
    intro hf
    have R2 : forall {x y y'}, Sat M ψ (Env.cons x (Env.cons y' e)) ->
        Sat M (rename Ax_r2 ψ) (Env.cons y' (Env.cons y (Env.cons x e))) := fun h =>
      (sat_rename ψ Ax_r2 _).2
        (Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _) h)
    have R1' : forall {x y y'}, Sat M ψ (Env.cons x (Env.cons y e)) ->
        Sat M (rename Ax_r1 ψ) (Env.cons y' (Env.cons y (Env.cons x e))) := fun h =>
      (sat_rename ψ Ax_r1 _).2
        (Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _) h)
    have ⟨b, hb, hb'⟩ := hM.repl ψ e he (e 0) (he 0) fun x y y' hx hy hy' h1 h2 =>
      hf x (hM.trans (he 0) hx) hx y hy y' hy' (R1' (y' := y') h1) (R2 (y := y) h2)
    refine (sat_ex em).2 ⟨b, hb, fun y hy h => ?_⟩
    have ⟨x, _, hx⟩ := (sat_ex em).1 h
    have ⟨hxa, hs⟩ := (sat_and em).1 hx
    exact hb' x y hxa hy (Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _)
      ((sat_rename ψ Ax_r3 _).1 hs))
*)

(*Lemma con : Con ZF := Con.of_model em (hM.valid em) PSet.empty hM.empty*)

End ZFModel.
