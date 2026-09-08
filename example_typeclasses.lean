import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

class MyGroup (α: Type*) where
  op: α → α → α
  op_inv: α → α
  id: α
  assoc (m: α) (n: α) (r: α): (op (op m n) r) = (op m (op n r))
  idem: ∀ m: α, ((op m id) = m) ∧ ((op id m) = m)
  inverse: ∀ m: α, ((op m (op_inv m)) = id) ∧ ((op (op_inv m) m) = id)
