Require Import Fml PSet Pair VLevel.
Definition Valid M f := forall e, Sat M f e.
Parameter Con : (Fml -> Prop) -> Prop.
(*!
`ZF` as a first-order theory: extensionality, foundation, pairing, union, power set, infinity,
and the schemas of separation and replacement. Free variables of an axiom are parameters. The
replacement schema is in its usual form "a functional relation on `a` has its values in some
`b`"; with separation this gives the image.

`ZFModel M` lists closure conditions on a class of sets which make every axiom valid in it.
*)


(*- `forallz (z ∈ x <-> z ∈ y) -> x = y` *)
Definition Ax_ext : Fml := imp (all (iff (mem 0 1) (mem 0 2))) (eq 0 1).

(*- `existsz z ∈ x -> existsy (y ∈ x /\ forallz (z ∈ y -> z ∉ x))` *)
Definition Ax_found : Fml :=
  imp (ex (mem 0 1)) (ex (and (mem 0 1) (all (imp (mem 0 1) (neg (mem 0 2)))))).

(*- `existsz (x ∈ z /\ y ∈ z)` *)
Definition Ax_pair : Fml := ex (and (mem 1 0) (mem 2 0)).

(*- `existsu forally forallz (z ∈ y -> y ∈ x -> z ∈ u)` *)
Definition Ax_union : Fml := ex (all (all (imp (mem 0 1) (imp (mem 1 3) (mem 0 2))))).

(*- `existsp forally (forallz (z ∈ y -> z ∈ x) -> y ∈ p)` *)
Definition Ax_power : Fml := ex (all (imp (all (imp (mem 0 1) (mem 0 3))) (mem 0 1))).

(*- `existsw (existse (e ∈ w /\ forallz z ∉ e) /\ forally (y ∈ w -> existss (s ∈ w /\ forallz (z ∈ s <-> z ∈ y \/ z = y))))` *)
Definition Ax_inf : Fml :=
  ex (and (ex (and (mem 0 1) (all (neg (mem 0 1)))))
    (all (imp (mem 0 1) (ex (and (mem 0 2) (all (iff (mem 0 1) (or (mem 0 2) (eq 0 2))))))))).

Definition sepR (k:nat) : nat :=
  match k with
  | 0 => 0
  | S n => S(S n)
  end.

(*- `existsy forallz (z ∈ y <-> z ∈ x /\ ψ(z, params))`, where `ψ` has `z` as variable `0` and the free
variables of the axiom (`x` among them) as its variables `n+1`. *)
Definition Ax_sep (ψ : Fml) : Fml := ex (all (iff (mem 0 1) (and (mem 0 2) (rename sepR ψ)))).

Definition r1 (k:nat) : nat :=
  match k with
  | 0 => 2
  | 1 => 1
  | S (S n) => S(S(S n))
  end.

Definition r2 (k:nat) : nat :=
  match k with
  | 0 => 2
  | 1 => 0
  | S(S n) => S(S(S n))
  end.

Definition r3 (k:nat) : nat :=
  match k with
  | 0 => 0
  | 1 => 1
  | S(S n) => S(S(S n))
  end.

(*- `forallx (x ∈ a -> forally forally' (ψ(x,y) -> ψ(x,y') -> y = y')) -> existsb forally (existsx (x ∈ a /\ ψ(x,y)) -> y ∈ b)`,
where `ψ` has `x`, `y` as variables `0`, `1` and the free variables of the axiom (`a` among
them) as its variables `n+2`. *)
Definition Ax_repl (ψ : Fml) : Fml :=
  imp (all (imp (mem 0 1) (all (all (imp (rename r1 ψ) (imp (rename r2 ψ) (eq 1 0)))))))
    (ex (all (imp (ex (and (mem 0 3) (rename r3 ψ))) (mem 0 1)))).

(*- The axioms of `ZF`. *)
Inductive ZF : Fml -> Prop :=
  | V_ext : ZF Ax_ext
  | V_found : ZF Ax_found
  | V_pair : ZF Ax_pair
  | V_union : ZF Ax_union
  | V_power : ZF Ax_power
  | V_inf : ZF Ax_inf
  | V_sep (ψ : Fml) : ZF (Ax_sep ψ)
  | V_repl (ψ : Fml) : ZF (Ax_repl ψ).

(*- Closure conditions on a class which make it a model of `ZF`. *)
Class ZFModel (M : PSet -> Prop) : Prop := {
  M_trans : forall {x z}, M x -> z ∈ x -> M z;
  M_empty : M empty;
  M_upair : forall {x y}, M x -> M y -> M (upair x y);
  M_sUnion : forall {x}, M x -> M (sUnion x);
  M_powerset : forall {x}, M x -> M (powerset x);
  M_omega : M omega;
  M_sep : forall (P : PSet -> Prop) {x}, M x -> M (sep P x);
  M_repl : forall (ψ : Fml) (e : nat -> PSet), (forall i, M (e i)) -> forall a, M a ->
    (forall x y y', x ∈ a -> M y -> M y' -> Sat M ψ (Env_cons x (Env_cons y e)) ->
      Sat M ψ (Env_cons x (Env_cons y' e)) -> y ≈ y') ->
    exists b, M b /\ forall x y, x ∈ a -> M y -> Sat M ψ (Env_cons x (Env_cons y e)) -> y ∈ b
  }.

(*- Every nonempty subset of a set has an `∈`-minimal element. *)
Lemma exists_minimal (em : forall p : Prop, p \/ ~p) (x : PSet) :
  forall z, z ∈ x -> exists y, y ∈ x /\ forall w, w ∈ y -> ~ w ∈ x.
Admitted.
(*  intro z
  induction z using mem_induction with | _ z ih => ?_
  intro hz
  rcases em (exists w, w ∈ z /\ w ∈ x) with ⟨w, hw, hwx⟩ | h
  · exact ih w hw hwx
  · exact ⟨z, hz, fun w hw hwx => h ⟨w, hw, hwx⟩⟩*)

Section ZFModel.
Context {M : PSet -> Prop} (hM : ZFModel M) (em : forall p : Prop, p \/ ~p).

Lemma valid : forall φ, ZF φ -> Valid M φ.
Admitted.
(*intro φ h e he
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
      (sat_and em).2 ⟨mem_upair.2 (.inl (Equiv.refl _)), mem_upair.2 (.inr (Equiv.refl _))⟩⟩
  | union =>
    exact (sat_ex em).2 ⟨PSet.sUnion (e 0), hM.sUnion (he 0),
      fun y _ z _ hz hy => mem_sUnion.2 ⟨y, hy, hz⟩⟩
  | power =>
    exact (sat_ex em).2 ⟨PSet.powerset (e 0), hM.powerset (he 0),
      fun y hy h => mem_powerset.2 fun z hz => h z (hM.trans hy hz) hz⟩
  | inf =>
    refine (sat_ex em).2 ⟨PSet.omega, hM.omega, (sat_and em).2 ⟨?_, fun y _ hy => ?_⟩⟩
    · exact (sat_ex em).2 ⟨PSet.empty, hM.empty,
        (sat_and em).2 ⟨mem_omega.2 ⟨0, Equiv.refl _⟩, fun z _ hz => not_mem_empty z hz⟩⟩
    · have ⟨n, e'⟩ := mem_omega.1 hy
      refine (sat_ex em).2 ⟨ofNat (n+1), hM.trans hM.omega (mem_omega.2 ⟨n+1, Equiv.refl _⟩),
        (sat_and em).2 ⟨mem_omega.2 ⟨n+1, Equiv.refl _⟩, fun z _ => (sat_iff em).2 ?_⟩⟩
      refine mem_succ.trans <| .trans ?_ (sat_or em).symm
      exact or_congr (mem_congr_right e').symm ⟨fun h => h.trans e'.symm, fun h => h.trans e'⟩
  | sep ψ =>
    let P : PSet -> Prop := fun z => Sat M ψ (Env.cons z e)
    have hP : forall z z' : PSet, z ≈ z' -> P z -> P z' := fun _ _ ez h =>
      Sat.resp ψ (Env.cons_resp ez fun _ => Equiv.refl _) h
    refine (sat_ex em).2 ⟨PSet.sep P (e 0), hM.sep P (he 0), fun z _ => (sat_iff em).2 ?_⟩
    have hPz : P z <-> Sat M (rename Ax_sepR ψ) (Env.cons z (Env.cons (PSet.sep P (e 0)) e)) :=
      .trans (Sat.resp_iff (fun _ => Iff.rfl) ψ fun i => by cases i <;> exact Equiv.refl _)
        (sat_rename ψ Ax_sepR _).symm
    refine (mem_sep hP).trans ⟨fun ⟨a, b⟩ => (sat_and em).2 ⟨a, hPz.1 b⟩, fun h => ?_⟩
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

Lemma con : Con ZF.
Admitted.
  (* Con.of_model em (hM.valid em) PSet.empty hM.empty. *)

End ZFModel.
