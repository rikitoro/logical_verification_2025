import LoVe.LoVelib

/- ## Structured Proofs -/
theorem fst_of_two_props :
  ∀ a b : Prop, a → b → a :=
  fix a b : Prop
  assume ha : a
  assume hb : b
  show a from ha

theorem fst_of_two_props' :
  ∀ a b : Prop, a → b → a :=
  assume a : Prop
  assume b : Prop
  assume ha : a
  assume hb : b
  show a from ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  assume ha : a
  have hb : b := hab ha
  have hc : c := hbc hb
  show c from hc


/- ## Connectives and Quantifiers -/

theorem And_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
  assume hab : a ∧ b
  have ha : a :=
    And.left hab
  have hb : b :=
    And.right hab
  show b ∧ a from
    And.intro hb ha

theorem Forall.one_point {α : Type} (t : α) (P : α → Prop) :
  (∀x, x = t → P x) ↔ P t :=
  Iff.intro
  (
    assume hall : ∀ x, x = t → P x
    show P t from by
      apply hall t
      rfl
  )
  (
    assume hp : P t
    fix x : α
    assume heq : x = t
    show P x from by
      rw [heq]
      exact hp
  )

theorem Exists.one_point' {α : Type} (t : α) (P : α → Prop) :
  (∃ x : α, x = t ∧ P x) ↔ P t :=
  Iff.intro
  (
    assume hex : ∃ x : α, x = t ∧ P x
    show P t from
      Exists.elim hex
        (
          fix x : α
          assume hand : x = t ∧ P x
          have hxt : x = t :=
            And.left hand
          have hpx : P x :=
            And.right hand
          show P t from by
            rw [← hxt]
            exact hpx
        )
  )
  (
    assume hpt : P t
    show ∃ x : α, x = t ∧ P x from
      Exists.intro t
        (
          have tt : t = t := rfl
          show t = t ∧ P t from
            And.intro tt hpt
        )
  )
