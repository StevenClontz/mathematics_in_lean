import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  simp





example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x x_in_inv_img
  rw [image, preimage] at x_in_inv_img
  simp at x_in_inv_img
  rcases x_in_inv_img with ⟨ a, a_in_s, fa_eq_fx⟩
  have a_eq_x : a = x := h fa_eq_fx
  rw [← a_eq_x]
  exact a_in_s


example : f '' (f ⁻¹' u) ⊆ u := by
  intro x x_in_img_inv
  rw [preimage, image] at x_in_img_inv
  simp at x_in_img_inv
  rcases x_in_img_inv with ⟨ a, fa_in_u, fa_eq_x ⟩
  rw [← fa_eq_x]
  exact fa_in_u


example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  sorry

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  -- intro y; simp
  -- intro x h fxeq i
  -- use x
  -- exact ⟨h i, fxeq⟩
  intro y
  simp
  intro x h₁ h₂ i
  use x
  constructor
  · apply h₁
  · exact h₂

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  rw [InjOn]
  simp
  intro x zero_le_x y zero_le_y sqrts_eq
  calc
    x = (sqrt x) ^ 2 := by rw [sq_sqrt zero_le_x]
    _ = (sqrt y) ^ 2 := by rw [sqrts_eq]
    _ = y := by rw [sq_sqrt zero_le_y]


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  rw [InjOn]
  simp
  intro x zero_le_x y zero_le_y sqs_eq
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq zero_le_x]
    _ = sqrt (y ^ 2) := by rw [sqs_eq]
    _ = y := by rw [sqrt_sq zero_le_y]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · intro y_in_sqrt_img
    simp
    simp at y_in_sqrt_img
    rcases y_in_sqrt_img with ⟨ x, _, sqrt_x_eq_y⟩
    have : 0 ≤ sqrt x := sqrt_nonneg x
    linarith
  · simp
    intro zero_le_y
    use y^2
    constructor
    · apply pow_nonneg
      exact zero_le_y
    · apply sqrt_sq zero_le_y

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  · simp
    intro x x_sq_eq_y
    have : 0 ≤ x ^ 2 := by apply sq_nonneg
    linarith
  · simp
    intro zero_le_y
    use sqrt y
    exact sq_sqrt zero_le_y

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro g a
    apply g
    apply inverse_spec
    use a
  · intro g x y fx_eq_fy
    rw [LeftInverse] at g
    have : inverse f (f x) = x := by apply g
    rw [← this]
    have : inverse f (f y) = y := by apply g
    rw [← this]
    rw [fx_eq_fy]



example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro g a
    rw [Surjective] at g
    have : ∃x, f x = a := by apply g
    rcases this with ⟨ x, fx_eq_a ⟩
    rw [← fx_eq_a]
    apply inverse_spec
    use x
  · intro g a
    rw [Function.RightInverse, LeftInverse] at g
    use inverse f a
    apply g

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rw [Surjective] at surjf
  rcases surjf S with ⟨j, h⟩
  have j_not_in_S : j ∉ S := by
    intro j_in_S
    have : j ∉ f j := by apply j_in_S
    have : j ∈ f j := by
      rw [← h] at j_in_S
      exact j_in_S
    contradiction
  have j_in_S : j ∈ S := by
    rw [← h] at j_not_in_S
    apply j_not_in_S
  contradiction

end
