
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
  -- (a.num * b.denom + b.num * a.denom) * (a'.denom * b'.denom) =
  -- (a'.num * b'.denom + b'.num * a'.denom) * (a.denom * b.denom)
  calc
  _ = (a.num * b.denom + b.num * a.denom) * (a'.denom * b'.denom) := by rfl
  _ = a.num * b.denom * (a'.denom * b'.denom) + b.num * a.denom * (a'.denom * b'.denom) := by ring
  _ = a.num * a'.denom * b.denom * b'.denom + b.num * b'.denom * a.denom * a'.denom := by ac_rfl
  _ = a'.num * a.denom * b.denom * b'.denom + b'.num * b.denom * a.denom * a'.denom := by simp [ha, hb]
  _ = (a'.num * b'.denom + b'.num * a'.denom) * (a.denom * b.denom) := by ring


end Fraction


namespace Rat

def mk : Fraction → Rat := Quotient.mk Fraction.Setoid

instance Add : Add Rat := {
  add := Quotient.lift₂ (fun a b : Fraction ↦ mk (a + b)) <| by
    intro  a b a' b' ha hb
    simp
    apply Quotient.sound
    apply Fraction.Setoid_add ha hb
}



end Rat

namespace AlternativeDef

-- ## Alternative Definitions of the Rational Numbers

def Rat.IsCanonical (a : Fraction) : Prop :=
  Fraction.denom a > 0 ∧
  Nat.Coprime (Int.natAbs (Fraction.num a)) (Int.natAbs (Fraction.denom a))

def Rat : Type :=
  { a : Fraction // Rat.IsCanonical a }

end AlternativeDef


end LoVe
