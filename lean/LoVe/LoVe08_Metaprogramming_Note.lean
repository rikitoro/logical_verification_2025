
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

theorem hypothesis_example {α : Type} {p : α → Prop} {a : α}
  (hpa : p a) : p a := by
  hypothesis




























end LoVe
