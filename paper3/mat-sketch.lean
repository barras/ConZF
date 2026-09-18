/-
Sanity check for Definition "the materializing recursion" (paper3, section
"Accessibility on a big carrier gives Replacement"): the recursion typechecks in
Lean 4 core, axiom-free, with carrier and motive both `PSet.{u} : Type (u+1)`.
Only the definition and its unfolding equation are here; `D` stands for
"well-orderings of subsets of G ∪ ω" and is left abstract. Lemma mat is not formalized.
-/
universe u

inductive PSet : Type (u+1)
  | mk (α : Type u) (A : α → PSet) : PSet

namespace PSet
def Idx : PSet.{u} → Type u | ⟨α, _⟩ => α
def Func : (x : PSet.{u}) → x.Idx → PSet.{u} | ⟨_, A⟩ => A

def empty : PSet.{u} := ⟨PEmpty, PEmpty.elim⟩
def sUnion (a : PSet.{u}) : PSet.{u} :=
  ⟨Σ x : a.Idx, (a.Func x).Idx, fun ⟨x, y⟩ => (a.Func x).Func y⟩
def pair2 (a b : PSet.{u}) : PSet.{u} := ⟨ULift Bool, fun i => if i.down then a else b⟩
def sing (a : PSet.{u}) : PSet.{u} := pair2 a a
def succ (x : PSet.{u}) : PSet.{u} := sUnion (pair2 x (sing x))
def pr (a b : PSet.{u}) : PSet.{u} := pair2 (sing a) (pair2 a b)
/-- `{t | P}`: a set guarded by a proposition. -/
def guard (P : Prop) (t : P → PSet.{u}) : PSet.{u} :=
  ⟨ULift.{u} (PLift P), fun h => t h.down.down⟩
def tag (n s : PSet.{u}) : PSet.{u} := ⟨s.Idx, fun i => pr n (s.Func i)⟩
def one : PSet.{u} := sing empty
def two : PSet.{u} := succ one

variable (D : PSet.{u} → PSet.{u}) (uu : PSet.{u})

def labels (G : PSet.{u}) : PSet.{u} :=
  sUnion (pair2 (sing empty) (sUnion (pair2 (sing (tag one (D G))) (sing (tag two uu)))))

def step (R : PSet.{u} → PSet.{u} → Prop) (p : PSet.{u})
    (rec : (c : PSet.{u}) → R c p → PSet.{u}) : PSet.{u} :=
  let G := sUnion (guard (R (pr p empty) p) (fun h => rec (pr p empty) h))
  sUnion ⟨(labels D uu G).Idx, fun i =>
    let v := (labels D uu G).Func i
    sUnion (guard (R (pr p v) p) fun h => succ (rec (pr p v) h))⟩

def F (R : PSet.{u} → PSet.{u} → Prop) (p : PSet.{u}) (a : Acc R p) : PSet.{u} :=
  Acc.rec (motive := fun _ _ => PSet.{u}) (fun p _ ih => step D uu R p ih) a

theorem F_eq (R) (p : PSet.{u}) (a : Acc R p) :
    F D uu R p a = step D uu R p (fun c h => F D uu R c (a.inv h)) := by
  cases a; rfl
