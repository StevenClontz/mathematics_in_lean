import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

theorem min_symm : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  apply h
  apply h


example : min (min a b) c = min a (min b c) := by
  have h : ∀ x y z : ℝ, min (min x y) z ≤ min x y := by
    intro x y z
    apply min_le_left
  have g : ∀ a b c : ℝ,  min (min a b) c ≤ min a (min b c) := by
    intro a b c
    apply le_min
    · show min (min a b) c ≤ a
      apply le_trans (h a b c)
      apply min_le_left
    · show min (min a b) c ≤ min b c
      apply le_min
      · show min (min a b) c ≤ b
        rw [min_symm a b]
        apply le_trans (h b a c)
        apply min_le_left
      apply min_le_right
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    exact g a b c
  · show min a (min b c) ≤ min (min a b) c
    rw [min_symm a (min b c)]
    rw [min_symm (min a b) c]
    rw [min_symm b c]
    rw [min_symm a b]
    exact g c b a




theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  apply add_le_add_right
  apply min_le_left
  apply add_le_add_right
  apply min_le_right


example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  apply aux
  have h: ∀ x y z : ℝ, x + -z ≤ y → x ≤ y + z := by
    intro x y z
    intro h
    rw [← add_neg_cancel_right x z]
    rw [add_comm x z, add_comm y z, add_assoc]
    apply add_le_add_left
    apply h
  apply h
  apply le_min
  have g: min (a+c) (b+c) ≤ a+c := by
   apply min_le_left
  linarith [g]
  have g: min (a+c) (b+c) ≤ b+c := by
   apply min_le_right
  linarith [g]




#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h: |a + -b + b| ≤ |a + -b| + |b| := by
    apply abs_add
  rw [add_assoc, add_comm (-b) b, ← add_assoc] at h
  rw [add_neg_cancel_right, ← sub_eq_add_neg] at h
  linarith [h]





section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  · show x ∣  y * (x * z)
    apply dvd_mul_of_dvd_right
    apply dvd_mul_right
  · show x ∣ x ^ 2
    apply dvd_mul_left
  · show x ∣ w ^ 2
    rw [pow_two]
    apply dvd_mul_of_dvd_right
    apply h


end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  have h : ∀ x y : ℕ, Nat.gcd x y ∣ Nat.gcd y x := by
    intro x y
    rw [Nat.dvd_gcd_iff]
    constructor
    · apply Nat.gcd_dvd_right
    · apply Nat.gcd_dvd_left
  apply Nat.dvd_antisymm
  repeat apply h
end
