Require Import Rule VLevel NatInstance.
(*!
The definability rule (doc/main.tex, section 5).

`I η q x y` is an arbitrary notion of "`y` is the value at `x` of the function defined over
`V_η` with parameter `q`". For the theorem in the paper it is satisfaction of a formula over
`V_η`, with `q` a pair of a formula code and a parameter; nothing here depends on that.
A limit `η > ω` is *reachable* if some `I`-definable function with parameters of rank below some
`ν ∈ η` has values of rank unbounded in `η`. The rule gives every ordinal that is `0`, a successor,
`ω` or reachable a coherent assignment. So either every ordinal has one, and then Replacement
holds, or some ordinal is none of these, which is a limit above `ω` into which no definable
function from a smaller set is cofinal (for first-order `I`: a worldly cardinal).
*)

Import PSet Ord Pair Mat.

Section S.
Context (I : PSet -> PSet -> PSet -> PSet -> Prop).

(*- `(q, s)` defines, over `V_η`, a partial function on `s` with values of rank unbounded in `η`. *)
Definition Unb (η q s : PSet) : Prop :=
  (forall x y y', x ∈ s -> I η q x y -> I η q x y' -> y ≈ y') /\
  (forall x y, x ∈ s -> I η q x y -> rank y ∈ η) /\
  (forall ζ, ζ ∈ η -> exists x y, x ∈ s /\ I η q x y /\ ζ ∈ succ (rank y)).

(*- `η` is reached from parameters of rank below `ν`. *)
Definition Reach (η ν : PSet) : Prop := exists q s, rank q ∈ ν /\ rank s ∈ ν /\ Unb η q s.

Definition IsSucc (η : PSet) : Prop := exists ζ, η ≈ succ ζ.

(*- The case of the rule that uses definable functions. *)
Definition LimCase (η : PSet) : Prop := ~ IsSucc η /\ ~ η ≈ omega /\ exists ν, ν ∈ η /\ Reach η ν.

(*- The least `ν` from which `η` is reached, as the set of the `ν ∈ η` from which it is not. *)
Definition Gν (η : PSet) : PSet := sep (fun ν => ~ Reach η ν) η.

(*- The target of the child `a`. *)
Definition RuleA (η ξ : PSet) : Prop :=
  η ≈ succ ξ \/ (η ≈ omega /\ ξ ≈ empty) \/ (LimCase η /\ ξ ≈ Gν η).

(*- The target of the child `b w`. *)
Definition RuleB (η w ξ : PSet) : Prop :=
  (η ≈ omega /\ rank w ∈ omega /\ ξ ≈ rank w) \/
  (LimCase η /\ exists q s x y, w ≈ triple q s x /\ Unb η q s /\ x ∈ s /\ I η q x y /\ ξ ≈ rank y).

Definition rule (η : PSet) (l: Label) : PSet -> Prop :=
  match l with
  | a => RuleA η
  | b w => RuleB η w
  | c _ => fun _ => False
  end.
  
Lemma omega_not_succ {ζ : PSet} (h : omega ≈ succ ζ) : False.
assert (h' : ζ ∈ omega).
{apply mem_congr_right with (1:=h).
 apply mem_succ; right; apply Equiv_refl. }
destruct h' as (n,h'); simpl in h'.
apply (not_mem_self (succ ζ)).
apply mem_congr_right with (1:=h).
exists (S n); apply succ_congr; trivial.
Qed.

(*! ### Invariance *)

(*variable {I}*)
Variable (I_resp : forall {η η' q q' x x' y y' : PSet},
  η ≈ η' -> q ≈ q' -> x ≈ x' -> y ≈ y' -> I η q x y -> I η' q' x' y').
(*include I_resp*)

Lemma Unb_resp {η η' q q' s s' : PSet} (eη : η ≈ η') (eq : q ≈ q') (es : s ≈ s')
    (h : Unb η q s) : Unb η' q' s'.
assert (back : forall {x y}, I η' q' x y -> I η q x y).
{intros ??; apply I_resp; try apply Equiv_refl; apply Equiv_symm; trivial. }
split;[|split].
*intros x y y' hx h1 h2.
 apply back in h1; apply back in h2.
 revert h1 h2; apply h.
 apply mem_congr_right with (1:=es); trivial.
*intros x y hx h1.
 apply back in h1.
 apply mem_congr_right with (1:=eη).
 revert h1; apply h.
 apply mem_congr_right with (1:=es); trivial.
*intros ζ hζ.
 apply (mem_congr_right eη) in hζ.
 destruct h as (_,(_,h)).
 destruct h with (1:=hζ) as (x & y & hx & h1 & h2).
 exists x; exists y; split; [|split]; trivial.
 +apply mem_congr_right with (1:=es); trivial.
 +revert h1; apply I_resp; trivial; apply Equiv_refl.
Qed.

Lemma Reach_resp {η η' ν ν' : PSet} (eη : η ≈ η') (eν : ν ≈ ν') (h : Reach η ν) :
    Reach η' ν'.
destruct h as (q & s & hq & hs & h).
exists q; exists s; split; [|split].
*apply mem_congr_right with (1:=eν); trivial.
*apply mem_congr_right with (1:=eν); trivial.
*revert h; apply Unb_resp; trivial; apply Equiv_refl.
Qed.

(*omit I_resp in*)
Lemma IsSucc_resp {η η' : PSet} (e : η ≈ η') (h : IsSucc η) : IsSucc η'.
Proof using I.
destruct h as (ζ, h).
exists ζ.
apply Equiv_trans with (1:=Equiv_symm e); trivial.
Qed.
                      
Lemma LimCase_resp {η η' : PSet} (e : η ≈ η') (h : LimCase η) : LimCase η'.
destruct h as (h1 & h2 & ν & hν & h3).
split; [|split;[|exists ν; split]].
*intro; apply h1.
 revert H; apply @IsSucc_resp; apply Equiv_symm; trivial.
*intro; apply h2.
 apply Equiv_trans with (1:=e); trivial.
*apply mem_congr_right with (1:=e); trivial.
*revert h3; apply Reach_resp; trivial.
 apply Equiv_refl.
Qed.

Lemma mem_Gν {η z : PSet} : z ∈ Gν η <-> z ∈ η /\ ~ Reach η z.
unfold Gν; rewrite mem_sep; [reflexivity|].
intros ?? e h h'; apply h.
revert h'; apply Reach_resp; [apply Equiv_refl|apply Equiv_symm; trivial].
Qed.

Lemma Gν_resp {η η' : PSet} (e : η ≈ η') : Gν η ≈ Gν η'.
apply ext; intro.
unfold Gν.
rewrite !@mem_sep.
*apply and_iff_morphism.
 apply mem_congr_right; trivial.
 apply not_iff_morphism.
 split; apply Reach_resp; try apply Equiv_refl; trivial.
 apply Equiv_symm; trivial.
*intros ?? e' nr r; apply nr.
 revert r; apply Reach_resp; [apply Equiv_refl|apply Equiv_symm;trivial].
*intros ?? e' nr r; apply nr.
 revert r; apply Reach_resp; [apply Equiv_refl|apply Equiv_symm;trivial].
Qed.

Lemma rule_resp {η η' : PSet} {l l' : Label} {ξ ξ' : PSet}
    (eη : η ≈ η') (el : Label_Equiv l l') (eξ : ξ ≈ ξ') (h : rule η l ξ) : rule η' l' ξ'.
destruct el.
*destruct h as [h|[(h1, h2) | (h1, h2)]].
 +left.
  apply succ_congr in eξ.
  eauto using Equiv_trans, Equiv_symm.
 +right; left.
  apply Equiv_symm in eη, eξ.
  split; eauto using Equiv_trans.
 +right; right.
  assert (eη' := eη); apply Gν_resp in eη'.
  split; eauto using Equiv_trans, Equiv_symm.
  revert h1; apply LimCase_resp; trivial.
*destruct h as [(h1& h2& h3)| (h1& q& s& x& y& h2& h3& h4& h5& h6)].
 +left.
  apply rank_congr in H.
  apply mem_congr_left with (1:=H) in h2.
  split;eauto using Equiv_trans, Equiv_symm.
 +right.
  apply LimCase_resp with (1:=eη) in h1.
  apply Unb_resp with (1:=eη) (2:=Equiv_refl _) (3:=Equiv_refl _) in h3.
  apply I_resp with (1:=eη) (2:=Equiv_refl _) (3:=Equiv_refl _) (4:=Equiv_refl _) in h5.
  split;[|exists q;exists s;exists x;exists y];
    eauto 10 using Equiv_trans, Equiv_symm.
*contradiction.
Qed.

Lemma rule_func {η : PSet} {l : Label} {ξ ξ' : PSet}
    (h : rule η l ξ) (h' : rule η l ξ') : ξ ≈ ξ'.
destruct l as [|w|?].
*destruct h as [h|[(h, h2)|(h, h2)]];
   destruct h' as [h'|[(h'& h2')|(h', h2')]];
   try assert(e := Equiv_trans (Equiv_symm h) h'). 
 +apply succ_inj in e; trivial.
 +apply Equiv_symm in e; apply omega_not_succ in e; contradiction.
 +destruct h' as ([],_); red; eauto.
 +apply omega_not_succ in e; contradiction.
 +apply Equiv_trans with (1:=h2); apply Equiv_symm; trivial.  
 +destruct h' as (_&[]&_); red; eauto.
 +destruct h as ([],_); red; eauto.
 +destruct h as (_&[]&_); red; eauto.
 +apply Equiv_trans with (1:=h2); apply Equiv_symm; trivial.  
*destruct h as [(h1& ?& h3) | (h1& q& s& x& y& h2& h3& h4& h5& h6)];
   destruct h' as [(h1'& ?& h3') | (h1'& q'& s'& x'& y'& h2'& ?& ?& h5'& h6')].
 +apply Equiv_trans with (1:=h3); apply Equiv_symm; trivial.  
 +destruct h1' as (_&[]&_); red; eauto.
 +destruct h1 as (_&[]&_); red; eauto.
 +assert(e := Equiv_trans (Equiv_symm h2) h2'). 
  apply triple_inj in e; destruct e as (eq& _& ex).
  apply Equiv_symm in eq.
  apply Equiv_symm in ex.
  assert (h5'' := I_resp (Equiv_refl _) eq ex (Equiv_refl _) h5').
  apply Equiv_trans with (1:=h6).
  apply Equiv_trans with (2:=Equiv_symm h6').
  apply rank_congr.
  revert h5 h5''; apply h3; trivial.
*contradiction.  
Qed.

(*! ### The class of the rule *)

(*variable (I) in*)
Definition Good (η : PSet) : Prop :=
  η ≈ empty \/ IsSucc η \/ η ≈ omega \/ exists ν, ν ∈ η /\ Reach η ν.

(*variable (I) in*)
(*- Ordinals all of whose predecessors, and itself, are handled by one of the cases. *)
Definition Cls (η : PSet) : Prop := IsOrd η /\ forall μ, (μ ∈ η \/ μ ≈ η) -> Good μ.

(*omit I_resp in*)
Lemma Cls_resp {η η' : PSet} (e : η ≈ η') (h : Cls η) : Cls η'.
Proof using.
destruct h as (h1,h2); split;
  [revert h1; apply IsOrd_resp; trivial|].
intros; apply h2.
destruct H; [left|right].
*revert H; apply mem_congr_right; trivial.
*apply Equiv_trans with (2:=Equiv_symm e); trivial.
Qed.

(*omit I_resp in*)
Lemma Cls_mem {η ξ : PSet} (h : Cls η) (hξ : ξ ∈ η) : Cls ξ.
Proof using.  
destruct h as (h1,h2).
split.
*apply IsOrd_mem with (2:=hξ); trivial.
*intros μ hμ; apply h2; left.
 destruct hμ as [h3|h4];
   [apply IsOrd_trans with (2:=h3); trivial
   |apply mem_congr_left with (1:=h4); trivial].
Qed.

(*omit I_resp in*)
Lemma succN_congr {G G' : PSet} (e : G ≈ G') : forall n, succN n G ≈ succN n G'.
Proof using.
induction n; simpl succN; auto using succ_congr.
Qed.

(*omit I_resp in*)
Lemma succN_empty {G : PSet} (e : G ≈ empty) : forall n, succN n G ≈ ofNat n.
Proof using.
induction n; simpl succN; simpl ofNat; auto using succ_congr.
Qed.

Section em.
Hypothesis (em : forall p : Prop, p \/ ~p).

(*- In the limit case, the least `ν` is an element of `η` from which `η` is reached. *)
Lemma Gν_spec {η : PSet} (hη : IsOrd η) (h : LimCase η) :
  Gν η ∈ η /\ IsOrd (Gν η) /\ Reach η (Gν η).
assert (up : forall {ν ν'}, ν' ∈ η -> ν ∈ ν' -> Reach η ν -> Reach η ν').
{intros ?? hν' hν (q& s& hq& hs& hu).
 exists q; exists s; split; [|split]; trivial.
 *apply IsOrd_mem in hν'; trivial.
  apply (@IsOrd_trans _ _) with (2:=hq); trivial.
 *apply IsOrd_mem in hν'; trivial.
  apply (@IsOrd_trans _ _) with (2:=hs); trivial. }
assert (hG : IsOrd (Gν η)).
{split.
 *intros μ hμ μ' hμ'.
  apply mem_Gν in hμ.
  destruct hμ as (hμη, hμr).
  apply mem_Gν; split.
  +apply (@IsOrd_trans _ _) with (2:=hμ'); trivial.
  +intros h'; apply hμr.
   revert h'; apply up; trivial.
 *intros μ hμ.
  apply IsOrd_mem_trans.
  apply mem_Gν; trivial. }
assert (hmem : Gν η ∈ η).
{destruct (@IsOrd_subset em) with (1:=hG) (2:=hη) as [h'|e].
 {intros z hz; apply mem_Gν in hz; apply hz. }
 *trivial.
 *destruct h as (_& _& ν& hν& hr).
  apply mem_congr_right with (1:=e) in hν.
  apply mem_Gν in hν.
  destruct hν as (_,[]); trivial. }
split; [|split]; trivial.
edestruct em as [?|hn]; [eassumption|].
edestruct not_mem_self.
eapply mem_Gν; split; eassumption.
Qed.

Lemma rule_mem {η : PSet} {l : Label} {ξ : PSet} (hη : Cls η)
    (h : rule η l ξ) : ξ ∈ η /\ Cls ξ.
assert (ξ ∈ η).
{destruct l as [|w|].
 *destruct h as [h |[ (h1, h2) | (h1, h2)]].
  +apply mem_congr_right with (1:=h).
   apply mem_succ; right; apply Equiv_refl.
  +apply mem_congr_right with (1:=h1).
   exists 0; trivial.
  +apply mem_congr_left with (1:=h2).
   apply Gν_spec with (2:=h1).
   apply hη.
 *destruct h as [(h1& h2& h3) | (?& q& s& x& y& _& h3& h4& h5& h6)].
  +apply mem_congr_right with (1:=h1).
   apply mem_congr_left with (1:=h3); trivial.
  +apply mem_congr_left with (1:=h6).
   apply h3 with (2:=h5); trivial.
 *contradiction. }
split; [trivial|].
apply (Cls_mem hη H).
Qed.

Lemma rule_sup (U : PSet) {η G : PSet} (hη : Cls η)
    (hG : forall x, x ∈ G <-> exists ζ, rule η a ζ /\ x ∈ ζ) (x : PSet) :
  x ∈ η <-> exists l ξ, Avail D U G l /\ rule η l ξ /\ x ∈ succ ξ.
split.
2:{intros (l& ξ& ?& hr& hx).
   assert (hξ := proj1(rule_mem hη hr)).
   apply mem_succ in hx; destruct hx as [hx | e].
   *destruct hη; eapply (IsOrd_trans _) with (2:=hx); trivial.
   *apply mem_congr_left with (1:=e); trivial. }
1:{ (* -- `G` is the target of the child `a`*)
  intros hx.
  assert (hGa : forall {ζ}, rule η a ζ -> G ≈ ζ).
  {intros ζ hζ; apply ext; intros z.
   rewrite hG; split.
   *intros (ζ'& h1& h2).
    revert h2; apply mem_congr_right.
    revert hζ h1; apply rule_func.
   *exists ζ; auto. }
  destruct (em (IsSucc η)) as [(ζ, e) | hs];
    [|destruct (em (η ≈ omega)) as [hω | hω]].
  *exists a; exists ζ; split; [|split].
   +left; trivial.
   +left; trivial.
   +revert hx; apply mem_congr_right; apply Equiv_symm; trivial.
  *apply mem_congr_right with (1:=hω) in hx.
   rewrite mem_omega in hx.
   destruct hx as (n, e).
   assert (hGe : G ≈ empty).
   {apply hGa; right; left; split; [trivial|apply Equiv_refl]. }
   assert (hr : rank (ofNat n) ≈ ofNat n).
   {apply IsOrd_rank_equiv.
    apply isOrd_ofNat. }
   assert (hw : ofNat n ∈ D G).
   {eapply (mem_D_of_rank em) with (n:=S n).
    *apply @IsOrd_resp with (2:=isOrd_empty).
     apply Equiv_symm; trivial.
    *apply mem_congr_left with (1:=hr).
     simpl succN; apply mem_succ; right.
     apply Equiv_symm; apply succN_empty; trivial. }
   exists (b (ofNat n)); exists (rank (ofNat n)).
   split; [|split].
   +right; left; eexists; split; [eassumption|constructor;apply Equiv_refl].
   +left; split; [|split]; [trivial| |apply Equiv_refl].
    apply mem_congr_left with (1:=hr).
    rewrite mem_omega; exists n; apply Equiv_refl.
   +apply mem_succ; right.
    apply Equiv_trans with (1:=e); apply Equiv_symm; trivial.
  *assert (hL : LimCase η).
   {destruct (proj2 hη η) as [h|[h|[h|h]]]; [right; apply Equiv_refl|..].
    +apply mem_congr_right with (1:=h) in hx.
     apply not_mem_empty in hx; contradiction.
    +contradiction.
    +contradiction.
    +split;[|split]; trivial. }
   destruct @Gν_spec with (1:=proj1 hη)(2:=hL)
     as (_& hGo& q& s& hq& hs'& hu).
   assert (hGe : G ≈ Gν η).
   {apply hGa; right; right; split; [trivial|apply Equiv_refl]. }
   destruct (proj2 (proj2 hu) _ hx) as (x'& y& hx'& hI& hxy).
   assert (hw : triple q s x' ∈ D G).
   {apply (mem_D_of_rank em) with (n:=4);
       [revert hGo; apply IsOrd_resp; apply Equiv_symm; trivial|].
    eapply mem_congr_right; [eapply succN_congr;apply hGe|].
    apply (rank_triple_mem em); trivial.
    apply rank_mem in hx'.
    eapply (IsOrd_trans _) with (2:=hx'); trivial. }
   exists (b (triple q s x')); exists (rank y); split; [|split]; trivial.
   +right; left; eexists; split; [eassumption|constructor;apply Equiv_refl].
   +right; split; [trivial|].
    exists q; exists s; exists x'; exists y; split;[|split;[|split;[|split]]];
      trivial; apply Equiv_refl. }
Qed.

(*- The definability rule meets the one-node conditions, for the class `Cls I`. *)
Lemma worldly_rule (U : PSet) : Rule D U rule Cls.
split.
*exact @rule_func.
*exact @rule_resp.
*exact @Cls_resp.
*exact @rule_mem.
*exact (@rule_sup U).
Qed.

End em.

(*! ### The dichotomy *)

(*omit I_resp in
variable (I) in*)
(*- Either Replacement holds for every functional relation (any proposition, not only a
definable one), or there is an ordinal that is not `0`, not a successor, not `ω`, and into which
no `I`-definable function from parameters of smaller rank is cofinal. For first-order `I` the
latter is a worldly cardinal, and `V_ρ ⊨ ZF`. *)
Lemma dichotomy (em : forall p : Prop, p \/ ~p) :
    (forall (s : PSet) (φ : PSet -> PSet -> Prop),
      (forall {x x' y y'}, x ≈ x' -> y ≈ y' -> φ x y -> φ x' y') ->
      (forall {x y y'}, x ∈ s -> φ x y -> φ x y' -> y ≈ y') ->
      exists img : PSet, forall y, y ∈ img <-> exists x, x ∈ s /\ φ x y) \/
    exists ρ : PSet, IsOrd ρ /\ ~ ρ ≈ empty /\ ~ IsSucc ρ /\ ~ ρ ≈ omega /\
                       forall ν, ν ∈ ρ -> ~ Reach ρ ν.
destruct (em (exists ρ, IsOrd ρ /\ ~ Good ρ)) as [(ρ & hρ & hg) | hall ];
  [right|left].
*exists ρ; split; [trivial|split;[|split;[|split]]].
 +intros h; apply hg; left; trivial.
 +intros h; apply hg; right; left; trivial.
 +intros h; apply hg; right; right; left; trivial.
 +intros ν hν h; apply hg; do 3 right; exists ν; auto.
*intros s φ φ_resp φ_func.
 assert (good : forall η, IsOrd η -> Good η).
 {intros η hη.
  edestruct em as [h|h];[eassumption|].
  destruct hall; eauto. }
 assert (cls : forall η, IsOrd η -> Cls η).
 {intros η hη; split; [trivial|].
  intros μ hμ; apply good.
  destruct hμ as [h|e];
    [eapply IsOrd_mem with (1:=hη)
    |revert hη;apply IsOrd_resp; apply Equiv_symm]; trivial. }
 (*-- the ranks of the values*)
 pose (ψ (*: PSet -> PSet -> Prop*) := fun x η => exists y, φ x y /\ η ≈ rank y).
 edestruct @Rule.replacement with (1:=worldly_rule em s) (s:=s) (φ:=ψ) as (R, hR);
   trivial.
 {intros ???? ex eη (y & h1 & h2); exists y; split.
  *revert h1; apply φ_resp; [trivial|apply Equiv_refl].
  *apply Equiv_trans with (2:=h2).
   apply Equiv_symm; trivial. }
 {intros ??? hx (y & h1 & h2) (y' & h1' & h2').
  apply Equiv_trans with (1:=h2).
  apply Equiv_trans with (2:=Equiv_symm h2').
  apply rank_congr.
  revert h1 h1'; apply φ_func; trivial. }
 {intros ??? (y & ? & h2).
  apply cls.
  apply Equiv_symm in h2.
  apply IsOrd_resp with (1:=h2).
  apply isOrd_rank. }
 pose (p (*: PSet -> Prop*) := fun y => exists x, x ∈ s /\ φ x y).
 exists  (sep p (Vl R)); intros y.
 rewrite mem_sep.
 2:{intros z z' e (x & hx & h).
    exists x; split; [trivial|].
    revert h; apply φ_resp; [apply Equiv_refl|trivial]. }
 split; [destruct 1; trivial|].
 intros h; split; [|trivial].
 destruct h as (x & hx & hφ).
   assert (hr : rank y ∈ R).
 {apply hR.
  exists x; split; [trivial|].
  exists y; split; [trivial|].
  apply Equiv_refl. }
 apply (mem_Vl em).
 eapply mem_congr_left; [|eapply rank_mem; eassumption].
 apply Equiv_symm; apply IsOrd_rank_equiv.
 apply  (isOrd_rank y).
Qed.

End S.

Print Assumptions dichotomy.
