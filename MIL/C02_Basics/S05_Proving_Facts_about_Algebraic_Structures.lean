import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

#check (lt_iff_le_and_ne : x < y ↔ x ≤ y ∧ x ≠ y)

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

theorem my_inf_comm : x ⊓ y = y ⊓ x := by
  have h : ∀ x y : α, x ⊓ y ≤ y ⊓ x := by
    intro x y
    apply le_inf
    apply inf_le_right
    apply inf_le_left
  apply le_antisymm
  repeat apply h

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  have h : ∀ x y z : α, x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z) := by
    intro x y z
    apply le_inf
    apply le_trans inf_le_left
    apply le_trans inf_le_left
    apply le_refl
    apply le_inf
    apply le_trans inf_le_left
    apply inf_le_right
    apply inf_le_right
  apply le_antisymm
  apply h
  rw [
    inf_comm,
    my_inf_comm (x ⊓ y) z,
    my_inf_comm y z,
    my_inf_comm x y
  ]
  apply h

example : x ⊔ y = y ⊔ x := sup_comm --ok i get it...

theorem my_sup_assoc : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := sup_assoc

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := sup_inf_self

variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry








example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have g: 0 ≤ dist x y + dist y x := by
    rewrite [← dist_self x]
    apply dist_triangle
  rewrite [dist_comm y x] at g
  linarith
end
