import MathLib.Tactic
open Nat

example (x q : Nat) : 37 * x + q = 37 * x + q := by
  rfl

example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]
