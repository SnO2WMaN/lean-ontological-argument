import GodExistence.Basic

namespace GodExistence

section Argument

variable {α} {K : Model} {Φ Ψ : Property α K}

variable (Positive : Metaproperty α K)

/-- Emptyness is non-positive. -/
lemma emptyness_negative
  (positive_dillema : ∀ Φ, ⊧ Positive (∼Φ ·) ⭤ ∼Positive Φ)
  (positive_implies : ∀ Φ Ψ, ⊧ □(∀' (λ a => Φ a ➝ Ψ a)) ➝ Positive Φ ➝ Positive Ψ)
  : ⊧ ∼Positive (λ _ => ⊥ₘ) := by
  intro x;

  by_contra! hC;
  replace hC : x ∈ Positive (λ _ => ⊥ₘ) := not_not.mp $ Set.mem_compl_iff _ _ |>.not.mp hC;

  have : x ∈ ∼Positive (λ _ => ⊤ₘ) := positive_dillema _ x |>.mp (by simpa);
  have : x ∈ Positive (λ _ => ⊤ₘ) := positive_implies (λ _ => ⊥ₘ) _ _ ?_ ?_;
  contradiction;
  . grind;
  . assumption;

/-- Positive properties are possibly exemplified. -/
lemma possibly_exemplified_of_positive_property
  (positive_dillema : ∀ Φ, ⊧ Positive (∼Φ ·) ⭤ ∼Positive Φ)
  (positive_implies : ∀ Φ Ψ, ⊧ □(∀' (λ a => Φ a ➝ Ψ a)) ➝ Positive Φ ➝ Positive Ψ)
  : ⊧ Positive Φ ➝ ◇∃' Φ := by
  intro x hx;
  have := (not_imp_not.mpr $ positive_implies Φ (λ _ => ⊥ₘ) x) $ by
    dsimp [Formula.imp];
    push_neg;
    constructor;
    . assumption;
    . apply emptyness_negative Positive positive_dillema positive_implies;
  grind;


/-- `a` is Godlike if it possesses all positive properties. -/
def Godlike (Positive : Metaproperty α K) : Property α K := λ a => ∀' (λ Φ => Positive Φ ➝ Φ a)


/-- Possibly, God exists. -/
lemma possibly_exists_godlike
  (positive_dillema : ∀ Φ, ⊧ Positive (∼Φ ·) ⭤ ∼Positive Φ)
  (positive_implies : ∀ Φ Ψ, ⊧ □(∀' (λ a => Φ a ➝ Ψ a)) ➝ Positive Φ ➝ Positive Ψ)
  (godlike_positive : ⊧ Positive (Godlike Positive))
  : ⊧ ◇∃' (Godlike Positive) := by
  intro x;
  apply possibly_exemplified_of_positive_property Positive positive_dillema positive_implies;
  apply godlike_positive;

/-- An _essence_ of an individual is a property possessed by it and necessarily implying any of its properties. -/
def Essence (Φ : Property α K) : Property α K := λ a => Φ a ⋏ ∀' (λ Ψ : Property α K => Ψ a ➝ □(∀' (λ b => Φ b ➝ Ψ b)))

/-- Being Godlike is an essence of any Godlike being. -/
lemma godlike_ess
  (positive_dillema : ∀ Φ, ⊧ Positive (∼Φ ·) ⭤ ∼Positive Φ)
  (necessarily_positive_of_positive : ∀ Φ, ⊧ Positive Φ ➝ □Positive Φ)
  : ⊧ ∀' (λ a => Godlike Positive a ➝ Essence (Godlike Positive) a) := by
  intro x a ha;
  constructor;
  . assumption;
  . intro Ψ hΨ y Rxy b b_godlike_y;
    have Ψ_positive_x : x ∈ Positive Ψ := by
      by_contra! hC;
      have : Positive (∼Ψ ·) x := positive_dillema Ψ x |>.mpr hC;
      have : (∼Ψ a) x := ha _ this;
      contradiction;
    apply b_godlike_y;
    apply necessarily_positive_of_positive _ x Ψ_positive_x y Rxy;

def NecessaryExistence : Property α K := λ a => ∀' (λ Φ => Essence Φ a ➝ □∃' Φ)

/-- Necessarily, God exists. -/
theorem necessarily_exists_godlike [K.IsS5]
  (positive_dillema : ∀ Φ, ⊧ Positive (∼Φ ·) ⭤ ∼Positive Φ)
  (positive_implies : ∀ Φ Ψ, ⊧ □(∀' (λ a => Φ a ➝ Ψ a)) ➝ Positive Φ ➝ Positive Ψ)
  (necessarily_positive_of_positive : ∀ Φ, ⊧ Positive Φ ➝ □Positive Φ)
  (positive_godlike : ⊧ Positive (Godlike Positive))
  (positive_necessaryExistence : ⊧ Positive NecessaryExistence)
  : ⊧ □∃' (Godlike Positive) := by
  suffices ⊧ ◇□∃' (Godlike Positive) by apply valid_mdp valid_axiomFive this;
  intro x;
  obtain ⟨y, Rxy, ⟨a, a_godlike_y⟩⟩ : (◇∃' (Godlike Positive)) x := possibly_exists_godlike _ positive_dillema positive_implies positive_godlike x;
  use y;
  constructor;
  . assumption;
  . have H₁ : (Positive NecessaryExistence ➝ NecessaryExistence a) y := a_godlike_y NecessaryExistence;
    have H₂ : NecessaryExistence a y := H₁ $ positive_necessaryExistence y;
    apply H₂;
    apply godlike_ess _ positive_dillema necessarily_positive_of_positive y a a_godlike_y;


/-- God does not have any non-positive properties. -/
lemma godlike_flawlessness (positive_dillema : ∀ Φ, ⊧ Positive (∼Φ ·) ⭤ ∼Positive Φ)
  : ⊧ ∀' λ a => (Godlike Positive) a ➝ ∼Positive Φ ➝ ∼Φ a := by
  intro x a a_godlike h;
  exact a_godlike (∼Φ ·) $ positive_dillema Φ x |>.mpr h;

/-- There is only one God.  -/
theorem monotheism (positive_dillema : ∀ Φ, ⊧ Positive (∼Φ ·) ⭤ ∼Positive Φ)
  : ⊧ (∀' λ a => ∀' λ b => (Godlike Positive a ➝ Godlike Positive b ➝ (a ≡ₗ b))) := by
  intro x a b ha hb Φ;
  constructor;
  . intro h;
    apply hb;
    apply not_imp_not.mp $ godlike_flawlessness Positive positive_dillema x a ha;
    assumption;
  . intro h;
    apply ha;
    apply not_imp_not.mp $ godlike_flawlessness Positive positive_dillema x b hb;
    assumption;


theorem modal_collapse {φ : Formula K} [K.IsS5]
  (positive_dillema : ∀ Φ, ⊧ Positive (∼Φ ·) ⭤ ∼Positive Φ)
  (positive_implies : ∀ Φ Ψ, ⊧ □(∀' (λ a => Φ a ➝ Ψ a)) ➝ Positive Φ ➝ Positive Ψ)
  (necessarily_positive_of_positive : ∀ Φ, ⊧ Positive Φ ➝ □Positive Φ)
  (positive_godlike : ⊧ Positive (Godlike Positive))
  (positive_necessaryExistence : ⊧ Positive NecessaryExistence)
  : ⊧ φ ⭤ □φ := by
  intro x;
  constructor;
  . intro h y Rxy;
    have : (□∀' (λ a => Godlike Positive a ➝ φ)) x := by
      obtain ⟨a, ha⟩ := necessarily_exists_godlike _
        positive_dillema
        positive_implies
        necessarily_positive_of_positive
        positive_godlike
        positive_necessaryExistence x x K.refl;
      apply godlike_ess _ positive_dillema necessarily_positive_of_positive x a ha |>.2;
      exact h;
    obtain ⟨a, ha⟩ := necessarily_exists_godlike _
      positive_dillema
      positive_implies
      necessarily_positive_of_positive
      positive_godlike
      positive_necessaryExistence x y Rxy;
    apply this y Rxy a ha;
  . apply valid_axiomT;

end Argument


end GodExistence
