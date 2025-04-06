import LoVe.LoVelib

-- # Love 09 Operational Semantics

namespace LoVe

-- ## Minimalistic Imperative Language

/-
  S ::= skip
      | x := a
      | S; S
      | if b then S else b
      | while b do S
-/


#print State

inductive Stmt  : Type where
  | skip        : Stmt
  | assign      : String → (State → ℕ) → Stmt
  | seq         : Stmt → Stmt → Stmt
  | ifThenElse  : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo     : (State → Prop) → Stmt → Stmt

infix:90 "; " => Stmt.seq

def sillyLoop : Stmt :=
  Stmt.whileDo (fun s : State ↦ s "x" > s "y") (
    Stmt.skip;
    Stmt.assign "x" (fun s : State ↦ s "x" - 1)
  )

-- ## Big-Step Semantics

inductive BigStep : Stmt × State → State → Prop  where
  | skip s :
    BigStep (.skip, s) s
  | assign x a s :
    BigStep (.assign x a, s) (s[x ↦ a s])
  | seq S T s t u (hS : BigStep (S, s) t) (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true B S T s t (hcond : B s) (hbody : BigStep (S, s) t) :
    BigStep (.ifThenElse B S T, s) t
  | if_false B S T s t (hcond : ¬ B s) (hbody : BigStep (T, s) t) :
    BigStep (.ifThenElse B S T, s) t
  | while_true B S s t u (hcond : B s)
    (hbody : BigStep (S, s) t)
    (hrest : BigStep (.whileDo B S, t) u) :
    BigStep (.whileDo B S, s) u
  | while_false B S s (hcond : ¬ B s) :
    BigStep (.whileDo B S, s) s

infix:110 " ⟹ " => BigStep


theorem sillyLoop_from_1_BigStep :
  (sillyLoop, (fun _ ↦ 0)["x" ↦ 1])  ⟹ (fun _ => 0) := by
  rw [sillyLoop]
  apply BigStep.while_true
  . simp
  . apply BigStep.seq
    . apply BigStep.skip
    . apply BigStep.assign
  . simp
    apply BigStep.while_false
    simp

theorem BigStep_deterministic {Ss l r} (hl : Ss ⟹ l) (hr : Ss ⟹ r) : l = r := by
  sorry


end LoVe
