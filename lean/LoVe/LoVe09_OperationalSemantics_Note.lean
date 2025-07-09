import LoVe.LoVelib


/- # LoVe Demo 9: Operational Semantics -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 9.1 Formal Semantics -/

/- ## 9.2 A minimalistic Inperative Language -/

/- WHILE Language
  S ::= skip
      | x := a
      | S; S
      | if b then S else S
      | while b do S
-/

inductive Stmt : Type where
  | skip        : Stmt
  | assign      : String → (State → ℕ) → Stmt
  | seq         : Stmt → Stmt → Stmt
  | ifThenElse  : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo     : (State → Prop) → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/-
while (x > y) do
  skip;
  x = x - 1
-/

def sillyLoop : Stmt :=
  Stmt.whileDo (fun s ↦ s "x" > s "y") <|
    Stmt.skip;
    Stmt.assign "x" (fun s ↦ s "x" - 1)


/- ## 9.3 Big-Step Semantics -/

/-

---------------- SKIP
 (skip, s) => s

---------------------------- ASSIGN
 (x := a, s) => s[x ↦ a s]



-/
end LoVe
