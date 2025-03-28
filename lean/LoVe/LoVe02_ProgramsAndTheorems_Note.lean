
import LoVe.LoVelib

/- # LoVe Note 2: Programs and Theorems -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

/- ## Type Definitions -/

namespace MyNat

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

#check Nat
#check Nat.zero
#check Nat.succ
#check Nat.succ .zero

#print Nat

end MyNat

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp

#check AExp
#check AExp.num
#check AExp.num (-5)
#check AExp.add
#check AExp.add (.var "x") (.num 3)

#print AExp
#print AExp.add


namespace MyList

inductive List (α : Type) where
  | nil   : List α
  | cons  : α → List α → List α

#check List.nil
#check List.cons
#check List.cons 1 .nil

end MyList

/- ## Function Definition -/

def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

def add : ℕ → ℕ → ℕ
  | m, .zero    => m
  | m, .succ n  => .succ (add m n)

#eval add 2 7
#reduce add 2 7

def mul : ℕ → ℕ → ℕ
  | _, .zero    => .zero
  | m, .succ n  => add m (mul m n)

#eval mul 2 7

def power : ℕ → ℕ → ℕ
  | _, .zero    => 1
  | m, .succ n  => mul m (power m n)

#eval power 3 0
#eval power 3 3

def powerParam (m : ℕ) : ℕ → ℕ
  | .zero     => 1
  | .succ n   => mul m (powerParam m n)

def iter (α : Type) (z : α) (f : α → α) : ℕ → α
  | .zero     => z
  | .succ n   => f (iter α z f n)

def powerIter (m n : ℕ) : ℕ :=
  iter ℕ 1 (mul m) n

#eval powerParam 3 0
#eval powerParam 3 4

#eval powerIter 3 0
#eval powerIter 3 4


def eval (env : String → ℤ) : AExp → ℤ
  | .num i      => i
  | .var x      => env x
  | .add e₁ e₂  => eval env e₁ + eval env e₂
  | .sub e₁ e₂  => eval env e₁ - eval env e₂
  | .mul e₁ e₂  => eval env e₁ * eval env e₂
  | .div e₁ e₂  => eval env e₁ / eval env e₂

#eval eval (fun _ ↦ 7) (.div (.var "y") (.num 0))
#eval eval (fun _ ↦ 7) (.div (.var "y") (.num 2))


def append (α : Type) : List α → List α → List α
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x (append α xs ys)

#eval append ℕ [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]

def appendImplicit {α : Type} : List α → List α → List α
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x (appendImplicit xs ys)

#eval appendImplicit [3, 1] [4, 1, 5]
#eval @appendImplicit ℕ [3, 1] [4, 1, 5]
#eval @appendImplicit _ [3, 1] [4, 1, 5]

def appendPretty {α : Type} : List α → List α → List α
  | [],       ys => ys
  | x :: xs,  ys => x :: appendPretty xs ys

def reverse {α : Type} : List α → List α
  | []        => []
  | x :: xs   => reverse xs ++ [x]

/- Theorem Statements -/

theorem add_comm (m n) :
  add m n = add n m :=
  sorry




end LoVe
