variable (P Q R: Prop)

example : P → P := by
  intro ih
  exact ih

example : P → Q → P := by
  intro ih1 _
  exact ih1

theorem modusPonens : P → (P → Q) → Q := by
  intro ih1 ih2
  apply ih2
  exact ih1

theorem transitivity : (P → Q) → (Q → R) → (P → R) := by
  intro ih1 ih2 ih3
  apply ih2
  exact ih1 ih3

example : (P → Q → R) → (P → Q) → (P → R) := by
  intro ih1 ih2 ih3
  apply ih1
  exact ih3
  apply ih2
  exact ih3

variable (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intro _ h2 h3 h4 h5
  apply h3
  apply h4
  apply h2
  exact h5

example : (P → Q) → ((P → Q) → P) → Q := by
  intro h1 h2
  apply h1
  apply h2
  intro h3
  apply h1
  exact h3

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro h1 h2 h3
  apply h2
  intro _
  apply h1
  intro h5
  apply h3
  intro _
  exact h5

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro h1 h2 h3
  apply h1
  intro temp1
  apply h3
  apply h2
  exact temp1

example : (((P → Q) → Q) → Q) → (P → Q) := by
  intro h1 v1
  apply h1
  intro temp1
  apply temp1
  exact v1

example :
  (((P → Q → Q) → ((P → Q) → Q)) → R) →
  ((((P → P) → Q) → (P → P → Q)) → R) →
  (((P → P → Q) → ((P → P) → Q)) → R) → R := by
  intro _ h2 _
  apply h2
  intro t1 t2 _
  apply t1
  intro _
  exact t2
