import Mathlib.Data.Set.Basic

namespace GodExistence

structure KripkeModel where
  World : Type u
  Rel : World → World → Prop


namespace KripkeModel

variable {K : KripkeModel}

instance : CoeSort KripkeModel (Type u) := ⟨KripkeModel.World⟩
instance : CoeFun KripkeModel (λ K => K.World → K.World → Prop) := ⟨KripkeModel.Rel⟩

class IsReflexive (K : KripkeModel) : Prop where
  refl : ∀ {x : K}, K x x
export IsReflexive (refl)
attribute [grind .] refl

class IsTransitive (K : KripkeModel) : Prop where
  trans: ∀ {x y z : K}, K x y → K y z → K x z
export IsTransitive (trans)
attribute [grind <=] trans

class IsSymmetric (K : KripkeModel) : Prop where
  symm : ∀ {x y : K}, K x y → K y x
export IsSymmetric (symm)
attribute [grind <=] symm


alias IsKT := IsReflexive
alias IsK4 := IsTransitive
alias IsKB := IsSymmetric

class IsS4 (K : KripkeModel) extends K.IsKT, K.IsK4 where
class IsS5 (K : KripkeModel) extends K.IsS4, K.IsKB where

end KripkeModel



inductive Formula (α : Type) : Type
  | falsum : Formula α
  | verum : Formula α
  | and : Formula α → Formula α → Formula α
  | or : Formula α → Formula α → Formula α
  | all (P : α → Formula α) : Formula α
  | ex (P : α → Formula α) : Formula α
  | box : Formula α → Formula α
  | dia : Formula α → Formula α

abbrev Predicate (α : Type) := α → Formula α

namespace Formula

variable {α} {K : KripkeModel}

notation "⊥" => falsum
notation "⊤" => verum
infixl:75 " ⋏ " => and
infixl:74 " ⋎ " => or
prefix:80 "□" => box
prefix:80 "◇" => dia

-- notation:78 "∀' " P => all P
-- notation:78 "∃' " P => ex P

notation:78 "∀' " P "," a => all P a
notation:78 "∃' " P "," a => ex P a

@[grind]
def neg : Formula α → Formula α
  | ⊥ => ⊤
  | ⊤ => ⊥
  | φ ⋏ ψ => neg φ ⋎ neg ψ
  | φ ⋎ ψ => neg φ ⋏ neg ψ
  -- | ∀' P => ∃' (λ x => neg (P x))
  -- | ∃' P => ∀' (λ x => neg (P x))
  | ∀' P, φ => ∃' (λ x => neg (P x)), φ
  | ∃' P, φ => ∀' (λ x => neg (P x)), φ
  | □φ => ◇(neg φ)
  | ◇φ => □(neg φ)
prefix:80 "∼" => neg

abbrev imp (φ ψ : Formula α) := ∼φ ⋎ ψ
infixr:76 " ➝ " => imp

abbrev iff (φ ψ : Formula α) := (φ ➝ ψ) ⋏ (ψ ➝ φ)
infix:70 " ⭤ " => iff

end Formula


abbrev Predicate.neg (P : Predicate α) : Predicate α := λ x => ∼(P x)
prefix:85 "∼" => Predicate.neg

@[grind]
def Forces {K : KripkeModel} (x : K) : Formula α → Prop
  | ⊥ => False
  | ⊤ => True
  | φ ⋏ ψ => Forces x φ ∧ Forces x ψ
  | φ ⋎ ψ => Forces x φ ∨ Forces x ψ
  | ∀' P, φ => ∀ a : α, Forces x (P a) → Forces x φ
  | ∃' P, φ => ∃ a : α, Forces x (P a) ∧ Forces x φ
  -- | ∀' P, a => ∀ a, Forces x (P a)
  -- | ∃' P, a => ∃ a, Forces x (P a)
  | □φ => ∀ y, K x y → Forces y φ
  | ◇φ => ∃ y, K x y ∧ Forces y φ
infix:60 " ⊩ " => Forces

variable {K : KripkeModel} {x : K} {φ ψ χ : Formula α}

@[grind =] lemma forces_neg : (x ⊩ ∼φ) ↔ ¬(x ⊩ φ) := by induction φ generalizing x <;> grind;
@[grind =] lemma forces_imp : (x ⊩ φ ➝ ψ) ↔ (x ⊩ φ → x ⊩ ψ) := by grind;
@[grind =] lemma forces_iff : (x ⊩ φ ⭤ ψ) ↔ ((x ⊩ φ) ↔ (x ⊩ ψ)) := by grind;

@[grind]
def Valid (K : KripkeModel) (φ : Formula α) := ∀ x : K, x ⊩ φ
infixl:60 " ⊨ " => Valid

variable {Φ : Predicate α}

@[grind .] lemma valid_axiomK : K ⊨ □(φ ➝ ψ) ➝ (□φ ➝ □ψ) := by intro x; grind;

lemma valid_mDuality : K ⊨ ◇φ ⭤ ∼□(∼φ) := by intro x; grind;

lemma valid_qDuality : K ⊨ (∃' Φ) ⭤ ∼(∀' ∼Φ) := by intro x; grind;

@[grind .] lemma valid_LEM : K ⊨ φ ⋎ ∼φ := by grind;

@[grind =>] lemma valid_mdp (h₁ : K ⊨ φ ➝ ψ) (h₂ : K ⊨ φ) : K ⊨ ψ := by
  intro x;
  apply forces_imp.mp $ h₁ x;
  apply h₂;

@[grind =>]
lemma valid_impTrans (h₁ : K ⊨ φ ➝ ψ) (h₂ : K ⊨ ψ ➝ χ) : K ⊨ φ ➝ χ := by
  intro x;
  apply forces_imp.mpr;
  intro h₃;
  apply forces_imp.mp $ h₂ x;
  apply forces_imp.mp $ h₁ x;
  assumption;

@[grind <=] lemma valid_necessitation (h : K ⊨ φ) : K ⊨ □φ := by grind;

@[grind .] lemma valid_axiomT [K.IsReflexive] : K ⊨ □φ ➝ φ := by grind;

@[grind .] lemma valid_axiomTDual [K.IsReflexive] : K ⊨ φ ➝ ◇φ := by grind;

@[grind .] lemma valid_axiomFour [K.IsTransitive] : K ⊨ □φ ➝ □□φ := by grind;

@[grind .] lemma valid_axiomB [K.IsSymmetric] : K ⊨ ◇□φ ➝ φ := by grind;



section Argument

variable
  {K : KripkeModel} [K.IsS5]
  {IsPositive : Predicate α → Formula α}
  {Ax1a : K ⊨ ∀' P, IsPositive Φ ➝ ∼IsPositive (∼Φ)}
  {Ax1a : ∀ Φ : Predicate α, K ⊨ IsPositive Φ ➝ ∼IsPositive (∼Φ)}
  {Ax1b : ∀ Φ : Predicate α, K ⊨ ∼IsPositive Φ ➝ IsPositive (∼Φ)}
  {Ax2 : ∀ Φ Ψ : Predicate α, K ⊨ IsPositive Φ ⋏ □(∀' (λ x => Φ x → Ψ x)) ➝ IsPositive Ψ}

def Godlike : Predicate α := λ x => ∀' (λ P => IsPositive P ➝ P x)

variable
  {Ax3 : K ⊨ IsPositive Godlike}

variable
  {Ax4 : ∀ φ : Predicate α, K ⊨ IsPositive φ ➝ □(IsPositive φ)}

abbrev NecessaryExistence : Predicate α := by sorry;

variable
  {Ax5 : K ⊨ IsPositive NecessaryExistence}

end Argument



end GodExistence
