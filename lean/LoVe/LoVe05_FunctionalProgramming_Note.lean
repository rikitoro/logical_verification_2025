import LoVe.LoVelib

/- # LoVe Demo 5: Functional Programming -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

-- ## Structural Induction

theorem Nat.succ_ne_self (n : ℕ) :
  .succ n ≠ n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp [ih]

-- ## Structural Recursion

def fact : ℕ → ℕ
  | 0       => 1
  | n + 1   => (n + 1) * fact n

def factThreeCases : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 1 => (n + 1) * fact n

-- def illegal : ℕ → ℕ
--   | n => illegal n + 1
-- fail to show termination for
--   LoVe.illegal
-- with errors
-- failed to infer structural recursion:

opaque immoral : ℕ → ℕ

axiom immoral_eq (n : ℕ) :
  immoral n = immoral n + 1

theorem proof_of_False : False :=
  have hi : immoral 0 = immoral 0 + 1 :=
    immoral_eq 0
  have him : immoral 0 - immoral 0 = immoral 0 + 1 - immoral 0 := by
    rw [← hi]
  have h0eq1 : 0 = 1 := by
    simp at him
  show False from by simp at h0eq1

-- ## Pattern Matching Expressions

def bcount {α : Type} (p : α → Bool) : List α → ℕ
  | []      => 0
  | x :: xs =>
    match p x with
    | true  => bcount p xs + 1
    | false => bcount p xs

#eval bcount (fun n => n % 2 == 0) []
#eval bcount (fun n => n % 2 == 0) [1]
#eval bcount (fun n => n % 2 == 0) [1, 2]
#eval bcount (fun n => n % 2 == 0) [1, 2, 3]


def min (a b : ℕ) : ℕ :=
  if a ≤ b then a else b


-- ## Structures

structure RGB where
  red   : ℕ
  green : ℕ
  blue  : ℕ

namespace RGB_inductive

inductive RGB : Type where
  | mk : ℕ → ℕ → ℕ → RGB

def RGB.red : RGB → ℕ
  | .mk r _ _ => r

def RGB.green : RGB → ℕ
  | .mk _ g _ => g

def RBG.blue : RGB → ℕ
  | .mk _ _ b => b

end RGB_inductive


structure RGBA extends RGB where
  alpha : ℕ

def pureRed : RGB := .mk 0xff 0x00 0x00

def pureGreen : RGB := {
  red   := 0x00
  green := 0xff
  blue  := 0x00
}

def semitransparentGreen : RGBA := {
  pureGreen with
  alpha := 0x7f
}


def shuffle (c : RGB) : RGB := {
  red   := RGB.green c
  green := RGB.blue  c
  blue  := RGB.red   c
}

theorem shuffle_shuffle_shuffle (c : RGB) :
  shuffle (shuffle (shuffle c)) = c := by
  rfl

-- ## Type Classes

class Inhabited (α : Type) : Type where
  default : α

instance  Nat.Inhabited : Inhabited ℕ where
  default := 0

instance List.Inhabited {α : Type} : Inhabited (List α) := {
  default := []
}

instance Fun.Inhabited {α β : Type} [Inhabited β] :
  Inhabited (α → β) where
  default := fun _ : α ↦ Inhabited.default

instance Prod.Inhabited {α β : Type} [Inhabited α] [Inhabited β] :
  Inhabited (α × β) := {
    default := (Inhabited.default, Inhabited.default)
  }

def head {α : Type} [Inhabited α] : List α → α
  | []      => Inhabited.default
  | x :: _  => x

#eval head ([] : List ℕ)
#eval head ([] : List (ℕ × ℕ))


theorem head_head {α : Type} [Inhabited α] (xs : List α) :
  head [head xs] = head xs := rfl


class Zero (α : Type) where
  zero : α

class One (α : Type) where
  one : α

class Neg (α : Type) where
  neg : α → α

class Inv (α : Type) where
  inv : α → α

class Acc (α : Type) where
  add : α → α → α

class Mul (α : Type) where
  mul : α → α → α

class IsComutative (α : Type) (f : α → α → α) where
  comm : ∀ a b, f a b = f b a

class IsAssociative (α : Type) (f : α → α → α) where
  assoc := ∀ a b c, f (f a b) c = f a (f b c)

-- ## Lists

theorem head_head_cases {α : Type} [Inhabited α] (xs : List α) :
  head [head xs] = head xs := by
  cases xs with
  | nil => rfl
  | cons x xs => rfl

theorem head_head_match {α : Type} [Inhabited α] (xs : List α) :
  head [head xs] = head xs :=
  match xs with
  | .nil => by rfl
  | .cons x xs => by rfl

theorem injection_example {α : Type} (x y : α) (xs ys : List α) (h : x :: xs = y :: ys) :
  x = y ∧ xs = ys := by
  cases h
  simp

theorem distincness_example {α : Type} (y : α) (ys : List α) (h : [] = y :: ys) :
  False := by
  cases h

def map {α β : Type} (f :α → β) : List α → List β
  | []        => []
  | x :: xs   => f x :: map f xs

def mapArgs {α β : Type} : (α → β) → List α → List β
  | _, []       => []
  | f, x :: xs  => f x :: mapArgs f xs

theorem map_ident {α : Type} (xs : List α) :
  map (fun x ↦ x) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [map, ih]

theorem map_comp {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
  map g (map f xs) = map (fun x ↦ g (f x)) xs := by
  induction xs with
  | nil =>
    rfl
  | cons x xs ih =>
    simp [map, ih]

def tail {α : Type} : List α → List α
  | []      => []
  | _ :: xs => xs

def headOpt {α : Type} : List α → Option α
  | []        => .none
  | x :: _    => .some x

def headPre {α : Type} : (xs : List α) → xs ≠ [] → α
  | [],     hxs => by simp at *
  | x :: _, hxs => x

#eval headPre [3, 1, 4] (by simp)

def zip {α β : Type} : List α → List β → List (α × β)
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | [],      _       => []
  | _ :: _,  []      => []


def length {α : Type} : List α → ℕ
  | []      => 0
  | _ :: xs => length xs + 1

theorem min_add_add (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l := by
  cases Classical.em (m ≤ n) with
  | inl h => simp [min, h]
  | inr h => simp [min, h]

theorem min_add_add_match (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
  match Classical.em (m ≤ n) with
  | .inl h => by simp [min, h]
  | .inr h => by simp [min, h]

theorem min_add_add_if (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
  if h : m ≤ n then
    by simp [min, h]
  else
    by simp [min, h]

theorem length_zip {α β : Type} (xs : List α) (ys : List β) :
  length (zip xs ys) = min (length xs) (length ys) := by
  induction xs generalizing ys with
  | nil =>
    simp [length, min]
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp [zip, length, ih ys, min_add_add]

theorem map_zip {α α' β  β' : Type} (f : α → α') (g : β → β') :
  ∀ xs ys,
    map (fun ab : α × β ↦ (f $ Prod.fst ab, g $ Prod.snd ab))
      (zip xs ys) =
    zip (map f xs) (map g ys)
  | x :: xs, y :: ys => by simp [zip, map, map_zip]
  | [],      _       => by rfl
  | _ :: _,  []      => by rfl


-- ## Binary Trees

inductive Tree (α : Type) : Type
  | nil : Tree α
  | node : α → Tree α → Tree α → Tree α

def mirror {α : Type} : Tree α → Tree α
  | .nil        => .nil
  | .node a l r => .node a (mirror r) (mirror l)

theorem mirror_mirror {α : Type} (t : Tree α) :
  mirror (mirror t) = t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
    simp [mirror, ihl, ihr]

theorem mirror_mirror_calc {α : Type} :
  ∀ t : Tree α, mirror (mirror t) = t
  | .nil => by rfl
  | .node a l r => calc
    mirror (mirror (.node a l r))
    = mirror (.node a (mirror r) (mirror l)) := by
      rfl
    _ = .node a (mirror (mirror l)) (mirror (mirror r)) := by
      rfl
    _ = .node a l r := by
      simp [mirror_mirror_calc]

theorem mirror_Eq_nil_Iff {α : Type} :
  ∀ t : Tree α, mirror t = .nil ↔ t = .nil
  | .nil          => by simp [mirror]
  | .node _ _ _   => by simp [mirror]

-- ## Dependent Inductive Types

inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons (a : α) {n : ℕ} (v : Vec α n) : Vec α (n + 1)

#check Vec.nil
#check Vec.cons
#check Vec ℕ 2
#check  Vec.cons 3 (.cons 2 (.cons 1 .nil))

def listOfVec {α : Type} : ∀ {n : ℕ}, Vec α n → List α
  | _, .nil       => []
  | _, .cons a v  => a :: listOfVec v

def vecOfList {α : Type} :
  ∀ xs : List α, Vec α (length xs)
  | []        => .nil
  | x :: xs   => .cons x (vecOfList xs)

theorem length_listOfVec {α : Type} :
  ∀ (n : ℕ) (v : Vec α n), List.length (listOfVec v) = n
  | _, .nil      => by rfl
  | _, .cons a v => by
    simp [listOfVec, length_listOfVec]



end LoVe
