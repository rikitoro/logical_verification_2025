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
  induction hl generalizing r with
  | skip s =>
    cases hr with
    | skip => rfl
  | assign x a s =>
    cases hr with
    | assign => rfl
  | seq S T s t u hS hT hS_ih hT_ih =>
    cases hr with
    | seq _ _ _ t' _ hS' hT' =>
      cases hS_ih hS' with
      | refl =>
        cases hT_ih hT' with
        | refl => rfl
  | if_true B S T s t hcond hbody hbody_ih =>
    cases hr with
    | if_true _ _ _ _ _ hcond' hbody' =>
      apply hbody_ih hbody'
    | if_false _ _ _ _ _ hcond' hbody' =>
      contradiction
  | if_false B S T s t hcond hbody hbody_ih =>
    cases hr with
    | if_true _ _ _ _ _ hcond' hbody' =>
      contradiction
    | if_false _ _ _ _ _ hcond' hbody' =>
      apply hbody_ih hbody'
  | while_true B S s t u hcond hbody hrest hbody_ih hrest_ih =>
    cases hr with
    | while_true _ _ _ t' _ hcond' hbody' hrest' =>
      cases hbody_ih hbody' with
      | refl =>
        cases hrest_ih hrest' with
        | refl => rfl
    | while_false _ _ _ hcond' =>
      contradiction
  | while_false B S s hcond =>
    cases hr with
    | while_true _ _ _ t' _ hcond' hbody' hrest' =>
      contradiction
    | while_false _ _ _ hcond' =>
      rfl

@[simp]
theorem BigStep_skip_Iff {s t} :
  (Stmt.skip, s) ⟹ t ↔ t = s := by
  apply Iff.intro
  . intro h
    cases h with
    | skip => rfl
  . intro h
    rw [h]
    apply BigStep.skip

-- (x := a, s) ⟹ t
@[simp]
theorem BigStep_assign_Iff {x a s t} :
  (Stmt.assign x a, s) ⟹ t ↔ t = s [x ↦ a s] := by
  apply Iff.intro
  . intro h
    cases h with
    | assign => rfl
  . intro h
    rw [h]
    apply BigStep.assign

-- (S; T, s) ⟹ u
@[simp]
theorem BigStep_seq_Iff {S T s u} :
  (S; T, s) ⟹ u ↔ (∃ t, (S, s) ⟹ t ∧ (T, t) ⟹ u) := by
  apply Iff.intro
  . intro h
    cases h with
    | seq _ _ _ t _ hS hT =>
      apply Exists.intro t
      apply And.intro hS hT
  . intro h
    cases h with
    | intro t ht =>
      apply BigStep.seq _ _ _ t
      apply ht.left
      apply ht.right

 -- (if B then S else T, s) ⟹ t
@[simp]
theorem BigStep_if_Iff {B S T s t} :
  (Stmt.ifThenElse B S T, s) ⟹  t ↔
  (B s ∧ (S, s) ⟹ t) ∨ (¬ B s ∧ (T, s) ⟹ t) := by
  apply Iff.intro
  . intro h
    cases h with
    | if_true _ _ _ _ _ hcond hbody =>
      aesop
      -- apply Or.inl
      -- apply And.intro
      -- . exact hcond
      -- . exact hbody
    | if_false _ _ _ _ _ hcond hbody =>
      aesop
      -- apply Or.inr
      -- apply And.intro
      -- . exact hcond
      -- . exact hbody
  . intro h
    cases h with
    | inl h =>
      apply BigStep.if_true
      . apply h.left
      . apply h.right
    | inr h =>
      apply BigStep.if_false
      . apply h.left
      . apply h.right


-- (while B do S, s) ⟹  u
theorem BigStep_while_Iff {B S s u} :
  (Stmt.whileDo B S, s) ⟹ u ↔
  (B s ∧ ∃ t, (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u)
  ∨ (¬ B s ∧ u = s) := by
  apply Iff.intro
  . intro h
    cases h with
    | while_true _ _ _ t _ hcond hbody hrest =>
      apply Or.inl
      apply And.intro
      . exact hcond
      . apply Exists.intro t
        apply And.intro hbody hrest
    | while_false _ _ _ hcond =>
      apply Or.inr
      apply And.intro hcond rfl
  . intro h
    cases h with
    | inl h =>
      cases h with
      | intro h h' =>
        cases h' with
        | intro t ht =>
          apply BigStep.while_true _ _ _ t _
          . apply h
          . apply ht.left
          . apply ht.right
    | inr h =>
      cases h with
      | intro hnB hus =>
        rw [hus]
        apply BigStep.while_false
        apply hnB

@[simp]
theorem BigStep_while_true_Iff {B S s u} (hcond : B s) :
  (Stmt.whileDo B S, s) ⟹ u ↔
  (∃ t, (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u) := by
  rw [BigStep_while_Iff]
  simp [hcond]

@[simp]
theorem BigStep_while_false_Iff {B S s t} (hcond : ¬ B s) :
  (Stmt.whileDo B S, s) ⟹ t ↔ t = s := by
  rw [BigStep_while_Iff]
  simp [hcond]

-- ## Small-Step Semantics

inductive SmallStep : Stmt × State → Stmt × State → Prop where
  | assign x a s :
    SmallStep (.assign x a, s) (.skip, s[x ↦ a s])
  | seq_step S S' T s s' (hS : SmallStep (S, s) (S', s')) :
    SmallStep (S; T, s) (S'; T, s')
  | seq_skip T s :
    SmallStep (.skip; T, s) (T, s)
  | if_true B S T s (hcond : B s) :
    SmallStep (.ifThenElse B S T, s) (S, s)
  | if_false B S T s (hcond : ¬ B s) :
    SmallStep (.ifThenElse B S T, s) (T, s)
  | whileDo B S s :
    SmallStep (.whileDo B S, s) (.ifThenElse B (S; .whileDo B S) .skip, s)

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

theorem sillyLoop_from_1_SmallStep :
  (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⇒*
  (.skip, (fun _ ↦ 0)) := by
  rw [sillyLoop]
  apply RTC.head
  . apply SmallStep.whileDo
  . apply RTC.head
    . apply SmallStep.if_true
      aesop
    . apply RTC.head
      . apply SmallStep.seq_step
        apply SmallStep.seq_skip
      . apply RTC.head
        . apply SmallStep.seq_step
          apply SmallStep.assign
        . apply RTC.head
          . apply SmallStep.seq_skip
          . apply RTC.head
            . apply SmallStep.whileDo
            . apply RTC.head
              . apply SmallStep.if_false
                simp
              . simp
                apply RTC.refl

-- ## Properties of the Small-Step Semantics

#print Stmt

theorem SmallStep_final (S s) :
  (¬ ∃ T t, (S, s) ⇒(T, t)) ↔ S = .skip := by
  induction S with
  | skip =>
    simp
    intro T t hstep
    cases hstep
  | assign x a =>
    simp
    apply Exists.intro .skip
    apply Exists.intro (s[x ↦ a s])
    apply SmallStep.assign
  | seq S T ihS ihT =>
    simp
    cases Classical.em (S = .skip) with
    | inl h =>
      rw [h]
      apply Exists.intro T
      apply Exists.intro s
      apply SmallStep.seq_skip
    | inr h =>
      simp [h] at ihS
      cases ihS with
      | intro S' hS' =>
        cases hS' with
        | intro s' hSs' =>
          apply Exists.intro (S'; T)
          apply Exists.intro s'
          apply SmallStep.seq_step
          exact hSs'
  | ifThenElse B S T ihS ihT =>
    simp
    cases Classical.em (B s) with
    | inl h =>
      apply Exists.intro S
      apply Exists.intro s
      apply SmallStep.if_true
      apply h
    | inr h =>
      apply Exists.intro T
      apply Exists.intro s
      apply SmallStep.if_false
      apply h
  | whileDo B S ihS =>
    simp
    apply Exists.intro <| .ifThenElse B (S; .whileDo B S) .skip
    apply Exists.intro s
    apply SmallStep.whileDo

#print SmallStep

theorem SmallStep_deterministic {Ss Ll Rr}
  (hl : Ss ⇒ Ll) (hr : Ss ⇒ Rr) : Ll = Rr := by
  induction hl generalizing Rr with
  | assign x a s =>
    cases hr with
    | assign _ _ _ => rfl
  | seq_step S S' T s s' hS ihS =>
    cases hr with
    | seq_step _ S'' _ _ s'' hS'' =>
      have h' := ihS hS''
      aesop
    | seq_skip =>
      cases hS
  | seq_skip T s =>
    cases hr with
    | seq_step _ S' _ _ s' hSkip =>
      cases hSkip
    | seq_skip => rfl
  | if_true B S T s hB =>
    cases hr with
    | if_true => rfl
    | if_false => contradiction
  | if_false B S T s hB =>
    cases hr with
    | if_true => contradiction
    | if_false => rfl
  | whileDo B S s =>
    cases hr with
    | whileDo => rfl



end LoVe
