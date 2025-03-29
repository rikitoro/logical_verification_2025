import LoVe.LoVelib

/- # LoVe Demo 5: Functional Programming -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

-- ## Structural Induction

theorem Nat.succ_ne_self (n : ℕ) :
  .succ n ≠ n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp [ih]

-- ## Structural Recursion

def fact : ℕ → ℕ
  | 0       => 1
  | n + 1   => (n + 1) * fact n

def factThreeCases : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 1 => (n + 1) * fact n

-- def illegal : ℕ → ℕ
--   | n => illegal n + 1
-- fail to show termination for
--   LoVe.illegal
-- with errors
-- failed to infer structural recursion:

opaque immoral : ℕ → ℕ

axiom immoral_eq (n : ℕ) :
  immoral n = immoral n + 1

theorem proof_of_False : False :=
  have hi : immoral 0 = immoral 0 + 1 :=
    immoral_eq 0
  have him : immoral 0 - immoral 0 = immoral 0 + 1 - immoral 0 := by
    rw [← hi]
  have h0eq1 : 0 = 1 := by
    simp at him
  show False from by simp at h0eq1

-- ## Pattern Matching Expressions

def bcount {α : Type} (p : α → Bool) : List α → ℕ
  | []      => 0
  | x :: xs =>
    match p x with
    | true  => bcount p xs + 1
    | false => bcount p xs

#eval bcount (fun n => n % 2 == 0) []
#eval bcount (fun n => n % 2 == 0) [1]
#eval bcount (fun n => n % 2 == 0) [1, 2]
#eval bcount (fun n => n % 2 == 0) [1, 2, 3]


def min (a b : ℕ) : ℕ :=
  if a ≤ b then a else b


-- ## Structures

structure RGB where
  red   : ℕ
  green : ℕ
  blue  : ℕ

namespace RGB_inductive

inductive RGB : Type where
  | mk : ℕ → ℕ → ℕ → RGB

def RGB.red : RGB → ℕ
  | .mk r _ _ => r

def RGB.green : RGB → ℕ
  | .mk _ g _ => g

def RBG.blue : RGB → ℕ
  | .mk _ _ b => b

end RGB_inductive


structure RGBA extends RGB where
  alpha : ℕ

def pureRed : RGB := .mk 0xff 0x00 0x00

def pureGreen : RGB := {
  red   := 0x00
  green := 0xff
  blue  := 0x00
}

def semitransparentGreen : RGBA := {
  pureGreen with
  alpha := 0x7f
}


def shuffle (c : RGB) : RGB := {
  red   := RGB.green c
  green := RGB.blue  c
  blue  := RGB.red   c
}

theorem shuffle_shuffle_shuffle (c : RGB) :
  shuffle (shuffle (shuffle c)) = c := by
  rfl

-- ## Type Classes

class Inhabited (α : Type) : Type where
  default : α

instance  Nat.Inhabited : Inhabited ℕ where
  default := 0

instance List.Inhabited {α : Type} : Inhabited (List α) := {
  default := []
}

instance Fun.Inhabited {α β : Type} [Inhabited β] :
  Inhabited (α → β) where
  default := fun _ : α ↦ Inhabited.default

instance Prod.Inhabited {α β : Type} [Inhabited α] [Inhabited β] :
  Inhabited (α × β) := {
    default := (Inhabited.default, Inhabited.default)
  }

def head {α : Type} [Inhabited α] : List α → α
  | []      => Inhabited.default
  | x :: _  => x

#eval head ([] : List ℕ)
#eval head ([] : List (ℕ × ℕ))


theorem head_head {α : Type} [Inhabited α] (xs : List α) :
  head [head xs] = head xs := rfl

end LoVe
