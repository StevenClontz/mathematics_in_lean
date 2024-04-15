import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro f_has_lb
  rcases f_has_lb with ⟨a, a_is_lb_for_f⟩
  rcases h a with ⟨x, fx_is_lt_a⟩
  have : f x ≥ a := a_is_lb_for_f x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨b, b_is_ub_for_f⟩
  have b_plus_one_le_b : b + 1 ≤ b := by
    apply b_is_ub_for_f
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro a_ge_b
  have : b ≤ a := by linarith
  have : f b ≤ f a := h this
  have : f a ≥ f b := by linarith
  apply not_lt_of_ge this
  exact h'



example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro f_is_mono
  have : f a ≤ f b := f_is_mono h
  have : f b ≥ f a := by linarith
  apply not_lt_of_ge this
  exact h'

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  push_neg
  let f := fun _ : ℝ ↦ (0 : ℝ)
  use f
  constructor
  · rw [Monotone]
    intro a b
    intro _
    dsimp
    apply le_refl
  · use 1
    use 0
    dsimp
    constructor <;> linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro x_gt_0
  let ε := x/2
  have : ε > 0  := by
    dsimp
    linarith
  have : x < x/2 := by
    apply h ε
    apply this
  linarith
end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro exists_x_Px
  rcases exists_x_Px with ⟨ x, Px⟩
  apply h x
  exact Px

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra not_exists_x_Px
  apply h
  intro x
  by_contra not_Px
  apply not_exists_x_Px
  use x

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro all_x_Px
  rcases h with ⟨ x, not_Px⟩
  apply not_Px
  apply all_x_Px x


example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (not_not_Q : ¬¬Q) : Q := by
  by_contra not_Q
  apply not_not_Q
  exact not_Q

example (h : Q) : ¬¬Q := by
  by_contra not_Q
  apply not_Q
  exact h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra no_x_fx_gt_a
  apply h
  rw [FnHasUb]
  use a
  rw [FnUb]
  intro x
  by_contra not_fx_lt_a
  apply no_x_fx_gt_a
  use x
  linarith


example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
