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
(x := x + y; y := 0, [x ↦ 3 , y ↦ 5]) ⟹ [x ↦ 8, y ↦ 0]
-/

/-

---------------- SKIP
 (skip, s) ⟹ s

---------------------------- ASSIGN
 (x := a, s) ⟹ s[x ↦ a s]

 (S, s) ⟹ t  (T, t) ⟹ u
--------------------------- SEQ
      (S; T, s) ⟹ u

 (S, s) ⟹ t
------------------------------- IF-TRUE if b s is true
 (if b then S else T, s) ⟹ t

 (T, s) ⟹ t
------------------------------- IF-TRUE if b s is false
 (if b then S else T, s) ⟹ t

 (S, s) ⟹ t   (while b do S, t) ⟹ u
--------------------------------------- WHILE-TRUE if b s is true
 (while b do S, s) ⟹ u

--------------------------- WHILE-FALSE if b s is false
 (while b do S, s) ⟹ s

where,
  s[x ↦ n] = (fun v ↦ if v = x then n else s v)

-/

/-
----------------------- ASSIGN  ------------------- ASSIGN
 (x := x + y, s) ⟹ t            (y := 0, t) => u
---------------------------------------------------- SEQ
 (x := x + y; y := 0, s) ⟹ u
-/

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hS : BigStep (S, s) t) (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : B s) (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ B s) (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : B s)
    (hbody : BigStep (S, s) t) (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s

infix:110 " ⟹ " => BigStep

theorem sillyLoop_from_1_BigStep :
  (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⟹ (fun _ ↦ 0) := by
  rw [sillyLoop]
  apply BigStep.while_true
  . simp
  . apply BigStep.seq
    . apply BigStep.skip
    . apply BigStep.assign
  . simp
    apply BigStep.while_false
    . simp

/- ## 9.4 Properties of the Big-Step Semantics -/

theorem BigStep_deterministic {Ss l r} (hl : Ss ⟹ l) (hr : Ss ⟹ r) :
  l = r := by
  induction hl generalizing r with
  | skip s =>
    cases hr with
    | skip => rfl
  | assign x a s =>
    cases hr with
    | assign => rfl
  | seq S T s t u hS hT ihS ihT =>
    cases hr with
    | seq _ _ _ t' _ hS' hT' =>
      apply ihS at hS'
      rw [← hS'] at hT'
      apply ihT at hT'
      exact hT'
  | if_true B S T s t hc hb ihb =>
    cases hr with
    | if_true _ _ _ _ _ hc' hb' =>
      apply ihb hb'
    | if_false _ _ _ _ _ hc' hb' =>
      contradiction
  | if_false B S T s t hc hb ih => sorry
  | while_true B S s t u hc hb hrest ihb ihrest  => sorry
  | while_false B S s hcond => sorry


end LoVe
