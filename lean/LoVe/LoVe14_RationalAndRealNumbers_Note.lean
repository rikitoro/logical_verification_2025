
import LoVe.LoVelib


-- # LoVe Demo 14: Rational and Real Numbers


set_option autoImplicit false
set_option tactic.hygienic false
namespace LoVe


-- ## Rational Numvers

structure Fraction where
  num             : ℤ
  denom           : ℤ
  denom_Neq_zero  : denom ≠ 0

namespace Fraction

instance Setoid : Setoid Fraction  where
  r := fun a b : Fraction ↦ num a * denom b = num b * denom a
  iseqv := {
    refl := by aesop
    symm := by aesop
    trans := by
      intro a b c hab hbc
      apply Int.eq_of_mul_eq_mul_right
      . apply denom_Neq_zero b
      . rw [mul_assoc, mul_comm c.denom, ← mul_assoc, hab]
        rw [mul_assoc c.num, mul_comm a.denom, ← mul_assoc, ← hbc]
        ac_rfl
  }

theorem Setoid_Iff (a b : Fraction) :
    a ≈ b ↔ num a * denom b = num b * denom a := by rfl

end Fraction

def Rat : Type :=
  Quotient Fraction.Setoid

namespace Fraction

instance Add : Add Fraction := {
  add := fun a b ↦ {
    num := num a * denom b + num b * denom a
    denom := denom a * denom b
    denom_Neq_zero := by simp [denom_Neq_zero]
  }
}

@[simp] theorem add_num (a b : Fraction) :
  num (a + b) = num a * denom b + num b * denom a := by rfl

@[simp] theorem add_denom (a b : Fraction) :
  denom (a + b) = denom a * denom b := by rfl

theorem Setoid_add {a a' b b' : Fraction} (ha : a ≈ a') (hb : b ≈ b') :
  a + b ≈ a' + b' := by
  simp [Setoid_Iff, add_num, add_denom] at *
  sorry

end Fraction

end LoVe
