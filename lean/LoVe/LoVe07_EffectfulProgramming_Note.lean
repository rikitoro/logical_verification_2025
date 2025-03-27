import LoVe.LoVelib

namespace LoVe

class LawfulMonad (m : Type → Type)
  extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β) :
    (pure a >>= f) = f a
  bind_pure {α : Type} (ma : m α) :
    (ma >>= pure) = ma
  bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ) (ma : m α) :
    (ma >>= f >>= g ) = (ma >>= fun a ↦ f a >>= g)

/- ## No Effects -/

def id.pure {α : Type} : α → id α
  | a => a

def id.bind {α β : Type} : id α → (α → id β) → id β
  | a, f => f a

instance id.LawfulMonad : LawfulMonad id where
  pure := pure
  bind := bind
  pure_bind := by
    intro α β a f
    rfl
  bind_pure := by
    intro α ma
    rfl
  bind_assoc := by
    intro α β γ f g ma
    rfl

/- ## Basic Exception -/

def Option.pure {α : Type} : α → Option α :=
  .some

def Option.bind {α β : Type} : Option α → (α → Option β) → Option β
  | .none, _ => .none
  | .some a, f => f a

instance Option.LawfulMonad : LawfulMonad Option where
  pure := Option.pure
  bind := Option.bind
  pure_bind := by
    intro α β a f
    rfl
  bind_pure := by
    intro α ma
    cases ma with
    | none => rfl
    | some a => rfl
  bind_assoc := by
    intro α β γ f g ma
    cases ma with
    | none => rfl
    | some a => rfl

/- ## Mutable State -/

def Action (σ α : Type) : Type := σ → α × σ

def Action.read {σ : Type} : Action σ σ
  | s => (s, s)

def Action.write {σ : Type} (s : σ) : Action σ Unit
  | _ => ((), s)

def Action.pure {σ α : Type} (a : α) : Action σ α
  | s => (a, s)

def Action.bind {σ α β : Type} (ma : Action σ α) (f : α → Action σ β) :
  Action σ β
  | s =>
    match ma s with
    | (a, s') => f a s'

instance Action.LawfulMonad {σ : Type} : LawfulMonad (Action σ) where
  pure := Action.pure
  bind := Action.bind
  pure_bind := by
    intro α β a f
    rfl
  bind_pure := by
    intro α ma
    rfl
  bind_assoc := by
    intro α β γ f g ma
    rfl

/- ## Nondeterminism -/

def Set.pure {α : Type} : α → Set α
  | a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
  | A, f => {b | ∃ a, a ∈ A ∧ b ∈ f a}

instance Set.LawfulMonad : LawfulMonad Set where
  pure := pure
  bind := bind
  pure_bind := by
    intro α β a f
    simp [pure, bind]
  bind_pure := by
    intro α ma
    simp [bind, pure]
  bind_assoc := by
    intro α β γ f g ma
    simp [bind]
    apply Set.ext
    intro x
    aesop

/- ## A Generic Algorithm : Iteration over a List -/

def nth {α : Type} : List α → ℕ → Option α
  | [],       _       => .none
  | x :: _,   0       => .some x
  | _ :: xs,  (n + 1) => nth xs n

def mmap {m : Type → Type} [LawfulMonad m] {α β : Type} (f : α → m β) :
  List α → m (List β)
  | []      => pure []
  | a :: as =>
    do
      let b ← f a
      let bs ← mmap f as
      pure <| b :: bs

def nthsCoarse {α : Type} (xss : List (List α)) (n : ℕ) :
  Option (List α) :=
  mmap (fun xs ↦ nth xs n) xss

#eval nthsCoarse [[11, 12, 13, 14], [21, 22, 23]] 2
#eval nthsCoarse [[11, 12, 13, 14], [21, 22, 23]] 3


theorem mmap_append {m : Type → Type} [LawfulMonad m]
  {α β : Type} (f : α → m β) :
  ∀ as as',
    mmap f (as ++ as') =
    do
      let bs ← mmap f as
      let bs' ← mmap f as'
      pure (bs ++ bs')
  | [], _ => by
    simp [mmap, LawfulMonad.bind_pure, LawfulMonad.pure_bind]
  | a :: as, as' => by
    simp [mmap, mmap_append, LawfulMonad.pure_bind, LawfulMonad.bind_assoc]


end LoVe
