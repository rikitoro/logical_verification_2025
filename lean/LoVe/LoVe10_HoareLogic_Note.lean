
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
  intro s t hs hst
  generalize ws_eq : (Stmt.whileDo B S, s) = Ss
  rw [ws_eq] at hst
  induction hst generalizing s with
  | skip          => cases ws_eq
  | assign        => cases ws_eq
  | seq           => cases ws_eq
  | if_true       => cases ws_eq
  | if_false      => cases ws_eq
  | while_true    =>
    cases ws_eq
    apply hrest_ih
    . apply h
      apply And.intro
      . apply hs
      . apply hcond
      apply hbody
    . rfl
  | while_false   =>
    cases ws_eq
    aesop

theorem consequence {P P' Q Q' S}
  (h : {* P *} (S) {* Q *}) (hp : ∀ s, P' s → P s) (hq : ∀ s, Q s → Q' s) :
  {* P' *} (S) {* Q' *} := by
  rw [PartialHoare] at *
  intro s t hs' hst
  apply hq
  apply h
  apply hp
  apply hs'
  apply hst

theorem consequence_left (P') {P Q S}
  (h : {* P *} (S) {* Q *}) (hp : ∀ s, P' s → P s) :
  {* P' *} (S) {* Q *} := by
  apply consequence <;> aesop

theorem consequence_right (Q) {Q' P S}
  (h : {* P *} (S) {* Q *}) (hq : ∀ s, Q s → Q' s) :
  {* P *} (S) {* Q' *} := by
  apply consequence <;> aesop

theorem skip_intro' {P Q} (h : ∀ s, P s → Q s) :
  {* P *} (.skip) {* Q *} := by
  apply consequence
  apply skip_intro
  . apply h
  . aesop

theorem assign_intro' {P Q x a} (h : ∀ s, P s → Q (s[x ↦ a s])) :
  {* P *} (.assign x a) {* Q *} := by
  apply consequence
  apply assign_intro
  . apply h
  . aesop

theorem  seq_intro' {P Q R S T} (hT : {* Q *} (T) {* R *}) (hS : {* P *} (S) {* Q *}) :
  {* P *} (S; T) {* R *} := by
  apply seq_intro <;> aesop

theorem while_intro' {B P Q S} (I)
  (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
  (hP : ∀ s, P s → I s)
  (hQ : ∀ s, ¬ B s → I s → Q s) :
  {* P *} (.whileDo B S) {* Q *} := by
  apply consequence
  apply while_intro
  apply hS
  aesop
  aesop

theorem assign_intro_forward (P) {x a} :
  {* P *} (.assign x a) {* fun s ↦ ∃ n₀, P (s[x ↦ n₀]) ∧ s x = a (s[x ↦ n₀]) *} := by
  apply assign_intro'
  intro s hs
  apply Exists.intro (s x)
  aesop

theorem assign_intro_backward (Q) {x a} :
  {* fun s ↦ ∃ n', Q (s[x ↦ n']) ∧ n' = a s *} (.assign x a) {* Q *} := by
  apply assign_intro'
  intro s hs
  cases hs with
  | intro n' =>
    aesop

-- ## Exchanging Two Variable

def SWAP : Stmt :=
  .assign "t" (fun s ↦ s "a");
  .assign "a" (fun s ↦ s "b");
  .assign "b" (fun s ↦ s "t")

theorem SWAP_correct (a₀ b₀ : ℕ) :
  {* fun s ↦ s "a" = a₀ ∧ s "b" = b₀ *}
  (SWAP)
  {* fun s ↦ s "a" = b₀ ∧ s "b" = a₀ *} := by
  apply seq_intro'
  apply seq_intro'
  apply assign_intro
  apply assign_intro
  apply assign_intro'
  aesop


#print BigStep

end PartialHoare



end LoVe
