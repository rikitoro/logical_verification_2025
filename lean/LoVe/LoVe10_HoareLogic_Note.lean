
import LoVe.LoVe08_Metaprogramming_Demo
import LoVe.LoVe09_OperationalSemantics_Demo

-- # LoVe Demo 10: Hoare Logic


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace LoVe


-- ## A Semantic Approach to Hoare Logic
#print State
#print Stmt

def PartialHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀ s t, P s → (S, s) ⟹ t → Q t

macro "{* " P:term " *} " "(" S:term ")" " {* " Q:term " *}" : term =>
  `(PartialHoare $P $S $Q)

namespace PartialHoare

theorem skip_intro {P} :
  {* P *} (.skip) {* P *} := by
  rw [PartialHoare]
  intro s t
  intro hPs hskip
  cases hskip
  apply hPs

theorem assign_intro (P) {x a} :
  {* fun s ↦ P (s[x ↦ a s]) *} (.assign x a) {* P *} := by
  rw [PartialHoare]
  intro s t hP hS
  cases hS with
  | assign =>
    exact hP

theorem seq_intro {P Q R S T} (hS : {* P *} (S) {* Q *}) (hT : {* Q *} (T) {* R *}) :
  {* P *} (S; T) {* R *} := by
  rw [PartialHoare] at *
  intro s t hP' hST
  cases hST with
  | seq =>
    apply hT
    apply hS
    apply hP'
    apply hS_1
    apply hT_1

theorem if_intro {B P Q S T}
  (hS : {* fun s ↦ P s ∧ B s *} (S) {* Q *})
  (hT : {* fun s ↦ P s ∧ ¬ B s *} (T) {* Q *}) :
  {* P *} (.ifThenElse B S T) {* Q *} := by
  rw [PartialHoare] at *
  intro s t hP' hif
  cases hif with
  | if_true =>
    apply hS
    apply And.intro
    . apply hP'
    . apply hcond
    apply hbody
  | if_false =>
    apply hT
    apply And.intro
    . apply hP'
    . apply hcond
    apply hbody


theorem while_intro (P) {B S}
  (h : {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
  {* P *} (.whileDo B S) {* fun s ↦ P s ∧ ¬ B s *} := by
  rw [PartialHoare] at *
  intro s t hPs hwhileBS
  sorry

end PartialHoare



end LoVe
