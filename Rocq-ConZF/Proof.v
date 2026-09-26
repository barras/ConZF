Require Import Fml.
(*!
A Hilbert-style proof system for first-order logic with `∈` and `=` (Mendelson's system with
de Bruijn variables): the axioms `K`, `S`, double negation elimination, instantiation of a
universal quantifier by a variable, distribution of `∀` over an implication whose antecedent
does not mention the bound variable, reflexivity of `=` and substitutivity of `=` in atomic
formulas; the rules modus ponens and generalization. The nonlogical axioms of a theory are
open formulas, their free variables standing for arbitrary parameters.

Soundness is proved for class models: if every axiom holds in `M` under every environment of
elements of `M`, so does every theorem. A theory with a nonempty model is consistent.
*)

Import PSet.

Inductive Prf (T : Fml -> Prop) : Fml -> Prop :=
  | Pax {φ} : T φ -> Prf T φ
  | Pk {φ ψ} : Prf T (imp φ (imp ψ φ))
  | Ps {φ ψ χ} : Prf T (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  | Pdne {φ} : Prf T (imp (neg (neg φ)) φ)
  | Pmp {φ ψ} : Prf T (imp φ ψ) -> Prf T φ -> Prf T ψ
  | Pgen {φ} : Prf T φ -> Prf T (all φ)
  | Pinst {φ} (j : nat) : Prf T (imp (all φ) (rename (inst j) φ))
  | Pdist {φ ψ} : Prf T (imp (all (imp (lift φ) ψ)) (imp φ (all ψ)))
  | Prefl (i : nat) : Prf T (eq i i)
  | Peq_mem_l (i j k : nat) : Prf T (imp (eq i j) (imp (mem i k) (mem j k)))
  | Peq_mem_r (i j k : nat) : Prf T (imp (eq i j) (imp (mem k i) (mem k j)))
  | Peq_eq (i j k : nat) : Prf T (imp (eq i j) (imp (eq i k) (eq j k))).

(*- `T` is consistent: it does not prove `⊥`. *)
Definition Con (T : Fml -> Prop) : Prop := ~ Prf T fls.

(*- `φ` holds in `M` under every environment of elements of `M`. *)
Definition Valid (M : PSet -> Prop) (φ : Fml) : Prop :=
  forall e : nat -> PSet, (forall i, M (e i)) -> Sat M φ e.

Lemma Env_cons_mem {M : PSet -> Prop} {x : PSet} {e : nat -> PSet} (hx : M x)
    (he : forall i, M (e i)) : forall i, M (Env_cons x e i).
destruct i; simpl; trivial.
Qed.

Lemma soundness (em : forall p : Prop, p \/ ~p) {T : Fml -> Prop} {M : PSet -> Prop}
  (hT : forall φ, T φ -> Valid M φ) {φ : Fml} (h : Prf T φ) : Valid M φ.
red in hT|-*.
induction h; simpl; intros e he; auto.
*apply (dne em).
*simpl in IHh1; auto.
*intros x hx; apply IHh; apply Env_cons_mem; trivial.
*intros h.
 rewrite sat_rename.
 generalize (h _ (he j)); apply Sat_resp.
 destruct i; apply Equiv_refl.
*intros h a x hx.
 apply h; trivial.
 unfold lift.
 rewrite sat_rename.
 exact a. (* uses eta *)
*apply Equiv_refl.
*intros e1; apply mem_congr_left with (1:=e1).
*intros e1; apply mem_congr_right with (1:=e1).
*eauto using Equiv_trans, Equiv_symm.
Qed.

(*- A theory with a nonempty class model is consistent. *)
Lemma Con_of_model (em : forall p : Prop, p \/ ~p) {T : Fml -> Prop} {M : PSet -> Prop}
    (hT : forall φ, T φ -> Valid M φ) (x : PSet) (hx : M x) : Con T.
intros h.
eapply (soundness em) with (1:=hT) (2:=h) (e:=fun _ => x); trivial.
Qed.
