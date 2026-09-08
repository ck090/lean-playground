open Classical

variable (p: Prop)

example : p → (¬ ¬ p) := by
  intro hp
  intro hnp
  contradiction

variable (α: Type)
variable (p q: α -> Prop)
variable (r: α -> α -> Prop)

example: (∀ x: α, (p x ∧ q x)) → (∀ x: α, p x) :=
  fun (h: ∀ x: α, (p x ∧ q x)) => (
    fun (z: α) => (h z).left
  )

example: (∃ x, p x) → (∃ x, (p x ∨ q z)) :=
  fun (hp: ∃ x, p x) => (
    match hp with
    | ⟨w, hw⟩ => ⟨w, Or.inl hw⟩
  )

example: (∃ x, ¬ p x) → (¬ ∀ x, p x) :=
  fun ⟨w, hw⟩ =>
    fun hpx: ∀ x, p x =>
      absurd (hpx w) (hw)

example: (∃ _: α, True) → (∀ x, p x) → (∃ x, p x) :=
  fun ⟨w, _⟩ => (
    fun h₁: (∀ x, p x) => (
      ⟨w, h₁ w⟩
    )
  )

def is_even (n: Nat) :=
  ∃ x: Nat, n = 2 * x
