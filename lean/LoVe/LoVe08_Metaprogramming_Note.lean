
import LoVe.LoVe06_InductivePredicates_Demo

-- # LoVe Demo 8: Metaprogramming

set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe

-- ## Tactic Combinators

theorem repeat'_first_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro
  repeat'
    first
    | apply Even.add_two
    | apply Even.zero
  . sorry
  . sorry

theorem all_goals_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro
  -- all_goals apply Even.add_two -- fails
  repeat' sorry


theorem all_goals_try_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro
  all_goals try apply Even.add_two
  repeat' sorry

theorem any_goals_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro
  any_goals apply Even.add_two
  repeat' sorry

theorem any_goals_example2 :
  Even 0 ∧ Even 0 ∧ Even 1 ∧ Even 0 := by
  repeat' apply And.intro
  -- any_goals apply Even.add_two -- fails
  repeat' sorry

theorem any_goals_solve_repeat_first_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro
  any_goals
    solve
    | repeat'
      first
      | apply Even.add_two
      | apply Even.zero
  sorry
  sorry

theorem repeat'_Not_example :
  ¬ Even 1 := by
  -- repeat' apply Not.intro
  sorry

-- # Macros

macro "intro_and_even" : tactic =>
  `(
    tactic |
    (
      repeat' apply And.intro
      any_goals
        solve
        | repeat'
          first
          | apply Even.add_two
          | apply Even.zero))


theorem intro_and_even_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  intro_and_even
  sorry
  sorry

-- ## Metaprogramming Monads

def traceGoals : TacticM Unit :=
  do
    logInfo m!"Lean Version {Lean.versionStringCore}"
    logInfo "All goals:"
    let goals ← getUnsolvedGoals
    logInfo m!"{goals}"
    match goals with
    | [] => return
    | _ :: _ =>
      logInfo "First goal's target:"
      let target ← getMainTarget
      logInfo m!"{target}"

elab "trace_goals" : tactic =>
  traceGoals

theorem Even_18_and_Even_20 (α : Type) (a : Type) :
  Even 18 ∧ Even 20 := by
  apply And.intro
  trace_goals
  intro_and_even

-- ## An Assumption Tactic

def hypothesis : TacticM Unit :=
  withMainContext (
    do
      let target ← getMainTarget
      let lctx ← getLCtx
      for ldecl in lctx do
        if ! LocalDecl.isImplementationDetail ldecl then
          let eq ← isDefEq (LocalDecl.type ldecl) target
          if eq then
            let goal ← getMainGoal
            MVarId.assign goal (LocalDecl.toExpr ldecl)
            return
      failure)

elab "hypothesis" : tactic =>
  hypothesis

theorem hypothesis_example {α : Type} {p : α → Prop} {a b: α}
  (h : p b → p a) (hpa : p a): p a := by
  hypothesis

-- ## Expressions

#check Expr
#print Expr


-- ## A conjuction-Destructing Tactic

theorem abc_a (a b c : Prop) (h : a ∧ b ∧ c) : a :=
  And.left h

theorem abc_b (a b c : Prop) (h : a ∧ b ∧ c) : b :=
  And.left (And.right h)

theorem abc_bc (a b c : Prop) (h : a ∧ b ∧ c) : b ∧ c :=
  And.right h

theorem abc_c (a b c : Prop) (h : a ∧ b ∧ c) : c :=
  And.right <| And.right h

partial def destructAndExpr (hP : Expr) : TacticM Bool :=
  withMainContext (
    do
      let target ← getMainTarget
      let P ← inferType hP
      let eq ← isDefEq P target
      if eq then
        let goal ← getMainGoal
        MVarId.assign goal hP
        return true
      else
        match Expr.and? P with
        | .none         => return false
        | .some (Q, R)  =>
          let hQ ← mkAppM ``And.left #[hP]
          let success ← destructAndExpr hQ
          if success then
            return true
          else
            let hR ← mkAppM ``And.right #[hP]
            destructAndExpr hR
  )

def destructAnd (name : Name) : TacticM Unit :=
  withMainContext (
    do
      let h ← getFVarFromUserName name
      let success ← destructAndExpr h
      if ! success then
        failure
  )

elab "destruct_and" h:ident : tactic =>
  destructAnd (getId h)

theorem abc_a_again (a b c : Prop) (h : a ∧ b ∧ c) : a := by
  destruct_and h

theorem abc_b_again (a b c : Prop) (h : a ∧ b ∧ c) : b := by
  destruct_and h

theorem abc_bc_again (a b c : Prop) (h : a ∧ b ∧ c) : b ∧ c := by
  destruct_and h

theorem abc_c_again (a b c : Prop) (h : a ∧ b ∧ c) : c := by
  destruct_and h

theorem abc_ab_again (a b c : Prop) (h : a ∧ b ∧ c) : a ∧ b := by
  -- destruct_and h --failed
  sorry

-- ## Direct Proof Finder

def isTheorem : ConstantInfo → Bool
  | .axiomInfo _  => true
  | .thmInfo _    => true
  | _             => false

def applyConstant (name : Name) : TacticM Unit :=
  do
    let cst ← mkConstWithFreshMVarLevels name
    liftMetaTactic (fun goal ↦ MVarId.apply goal cst)

def andThenOnSubgoals (tac₁ tac₂ : TacticM Unit) : TacticM Unit :=
  do
    let origGoals ← getGoals
    let mainGoal ← getMainGoal
    setGoals [mainGoal]
    tac₁
    let subgoals₁ ← getUnsolvedGoals
    let mut newGoals := []
    for subgoal in subgoals₁ do
      let assigned ← MVarId.isAssigned subgoal
      if ! assigned then
        setGoals [subgoal]
        tac₂
        let subgoals₂ ← getUnsolvedGoals
        newGoals := newGoals ++ subgoals₂
    setGoals (newGoals ++ List.tail origGoals)

def proveUsingTheorem (name : Name) : TacticM Unit :=
  andThenOnSubgoals (applyConstant name) hypothesis

def proveDirect : TacticM Unit :=
  do
    let origGoals ← getUnsolvedGoals
    let goal ← getMainGoal
    setGoals [goal]
    let env ← getEnv
    for (name, info) in SMap.toList (Environment.constants env) do
      if isTheorem info && ! ConstantInfo.isUnsafe info then
        try
          proveUsingTheorem name
          logInfo m!"Proved directly by {name}"
          setGoals (.tail origGoals)
          return
        catch _ =>
          continue
    failure

elab "prove_direct" : tactic =>
  proveDirect


theorem Nat.symm (x y : ℕ) (h : x = y) :
  y = x := by
  prove_direct

theorem Nat.symm_manual (x y : ℕ) (h : x = y) :
  y = x := by
  apply symm
  hypothesis















end LoVe
