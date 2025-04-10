
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

end LoVe
