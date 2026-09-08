import MathLib.Tactic

variable (P Q R : Prop)

example : true := by
  trivial

example : true → true := by
  intro ih
  exact ih

example : false → true := by
  intro ih
  exfalso
  trivial
