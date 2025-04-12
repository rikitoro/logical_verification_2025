
import LoVe.LoVe06_InductivePredicates_Demo


-- # LoVe Demo 13: Basic Mathematical Structures

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

-- ## Type Classes over a Single Binary Operator

class Group (α : Type) where
  mul           : α → α → α
  one           : α
  inv           : α → α
  mul_assoc     : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul       : ∀ a, mul one a = a
  mul_left_inv  : ∀ a, mul (inv a) a = one

inductive Int2 : Type
  | zero
  | one

def Int2.add : Int2 → Int2 → Int2
  | .zero,  a     => a
  | .one,   .zero => .one
  | .one,   .one  => .zero

instance Int2.AddGroup : AddGroup Int2 where
  add             := .add
  zero            := .zero
  neg             := id
  add_assoc       := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  zero_add        := by
    intro a
    cases a <;> rfl
  add_zero        := by
    intro a
    cases a <;> rfl
  neg_add_cancel  := by
    intro a
    cases a <;> rfl
  nsmul           :=
    @nsmulRec Int2 (Zero.mk .zero) (Add.mk .add)
  zsmul           :=
    @zsmulRec Int2 (Zero.mk .zero) (Add.mk .add)
      (.mk id)
      (@nsmulRec Int2 (Zero.mk .zero) (Add.mk .add))

#reduce Int2.one + 0 - 0 - Int2.one


instance List.addMonoid {α : Type} : AddMonoid (List α) where
  zero        := []
  add         := fun xs ys ↦ xs ++ ys
  add_assoc   := List.append_assoc
  zero_add    := List.nil_append
  add_zero    := List.append_nil
  nsmul       :=
    @nsmulRec (List α) (Zero.mk []) (Add.mk fun xs ys ↦ xs ++ ys)

-- ## Type Classes over Two Binary Operators

#print Field

def Int2.mul : Int2 → Int2 → Int2
  | .one,   a => a
  | .zero,  _ => .zero

theorem Int2.mul_assoc (a b c : Int2) :
  Int2.mul (.mul a b) c = .mul a (.mul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

instance Int2.Field : Field Int2 := {
  Int2.AddGroup with
  one := .one
  mul := .mul
  inv := id
  add_comm := by
    intro a b
    cases a <;> cases b <;> rfl
  exists_pair_ne := by
    apply Exists.intro .zero
    apply Exists.intro .one
    intro h
    cases h
  zero_mul := by
    intro a
    cases a <;> rfl
  mul_zero := by
    intro a
    cases a <;> rfl
  one_mul := by
    intro a
    rfl
  mul_one := by
    intro a
    cases a <;> rfl
  mul_inv_cancel := by
    intro a h
    cases a
    . apply False.elim
      apply h
      rfl
    . rfl
  inv_zero := by
    rfl
  mul_assoc := mul_assoc
  mul_comm := by
    intro a b
    cases a <;> cases b <;> rfl
  left_distrib := by
    intro a b c
    cases a <;> cases b <;> rfl
  right_distrib := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  nnqsmul := _
  nnqsmul_def := by
    intro a b
    rfl
  qsmul := _
  qsmul_def := by
    intro a b
    rfl
  nnratCast_def := by
    intro q
    rfl
}

#reduce (1 : Int2) * 0 / (0 - 1)
#reduce (3 : Int2)


-- ## Coercions

theorem neg_mul_neg_Nat (n : ℕ) (z : ℤ) :
  (- z) * (- n) = z * n := by
  simp

#check neg_mul_neg_Nat

theorem neg_Nat_mul_neg (n : ℕ) (z : ℤ) :
  (- n : ℤ) * (- z) = n * z := by
  simp

theorem Eq_coe_int_imp_Eq_Nat (m n : ℕ) (h : (m : ℤ) = (n : ℤ)) :
  m = n := by
  norm_cast at h

theorem Nat_coe_Int_add_eq_add_Nat_coe_Int (m n : ℕ) :
  (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) := by
  norm_cast

-- ## Lists, Multisets, and Finite Sets

def List.elems : Tree ℕ → List ℕ
  | .nil        => []
  | .node a l r => a :: elems l ++ elems r

def Multiset.elems : Tree ℕ → Multiset ℕ
  | .nil        => ∅
  | .node a l r => {a} ∪ elems l ∪ elems r

theorem Multiset.preserve_mirror (t : Tree ℕ) :
  elems t = elems (mirror t) := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
    simp [mirror, elems, ihl, ihr]
    sorry -- union のassoc が見当たらない

def Finset.elems : Tree ℕ → Finset ℕ
  | .nil          => ∅
  | .node a l r   => {a} ∪ elems l ∪ elems r

#eval List.sum [2, 3, 4, 4]
#eval Multiset.sum {2, 3, 4, 4}

#eval List.prod [2, 3, 4, 4]
#eval Multiset.prod {2, 3, 4, 4}

-- ## Order Type Classes

inductive Nat.le : ℕ → ℕ → Prop
  | refl : ∀ a, le a a
  | step : ∀ a b, le a b → le a (b + 1)

instance List.length.Preorder {α : Type} : Preorder (List α) where
  le := fun xs ys ↦ xs.length ≤ ys.length
  lt := fun xs ys ↦ xs.length < ys.length
  le_refl := by
    intro xs
    apply Nat.le_refl
  le_trans := by
    intro xs ys zs
    apply Nat.le_trans
  lt_iff_le_not_le := by
    intro a b
    apply Nat.lt_iff_le_not_le

theorem list.length.Preorder_example :
  [1] > [] := by
  decide



end LoVe
