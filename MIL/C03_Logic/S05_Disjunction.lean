import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg]
    exact h
  · rw [abs_of_neg]
    linarith
    exact h

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg]
    linarith
    exact h
  · rw [abs_of_neg]
    exact h

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 x with h | h
  · rcases le_or_gt 0 y with g | g
    · have : x + y ≥ 0 := by linarith
      repeat rw [abs_of_nonneg]
      repeat linarith
    · rcases le_or_gt 0 (x+y) with k | k
      · rw [abs_of_nonneg, abs_of_nonneg, abs_of_neg]
        repeat linarith
      · rw [abs_of_neg, abs_of_nonneg, abs_of_neg]
        repeat linarith
  · rcases le_or_gt 0 y with g | g
    · rcases le_or_gt 0 (x+y) with k | k
      · rw [abs_of_nonneg, abs_of_neg, abs_of_pos]
        repeat linarith
      · rw [abs_of_neg, abs_of_neg, abs_of_nonneg]
        repeat linarith
    · have : x + y < 0 := by linarith
      repeat rw [abs_of_neg]
      repeat linarith








theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  have : y≤|y| := by
    rcases le_or_gt 0 y with k | k
    · rw [abs_of_nonneg]
      apply k
    · rw [abs_of_neg]
      repeat linarith
  have : -y≤|y| := by
    rcases le_or_gt 0 y with k | k
    · rw [abs_of_nonneg]
      repeat linarith
    · rw [abs_of_neg]
      apply k
  constructor
  · intro g
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h] at g
      left
      apply g
    · rw [abs_of_neg h] at g
      right
      apply g
  · intro g
    rcases g with h | h
    · repeat linarith
    · rcases le_or_gt 0 y with _ | _
      · linarith
      · linarith




theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨ x, y, h₁, h₂ ⟩ <;>
  · have : x^2≥ 0:= by apply pow_two_nonneg
    have : y^2≥ 0:= by apply pow_two_nonneg
    linarith



example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by
    linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this
  · left; linarith
  · right; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x - y) * (x + y) = 0 := by
    linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this
  · left; linarith
  · right; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by
    ring_nf
    rw [h]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this
  · left; sorry
  · right; sorry


example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
