have lt_key :=

inductive MinHeap (α: Type) where
| hnil : MinHeap α
| hnode: Nat → α → MinHeap α → MinHeap α → MinHeap α
deriving Repr


example : MinHeap Nat := MinHeap.hnode 10 5 (MinHeap.hnode 12 8 MinHeap.hnil MinHeap.hnil ) (MinHeap.hnode 16 9 MinHeap.hnil MinHeap.hnil)
example : MinHeap Bool := MinHeap.hnode 12 true (MinHeap.hnode 15 false MinHeap.hnil MinHeap.hnil) (MinHeap.hnil)

-- Check if the root of the tree is either NIL or greater than the key
-- Prop is the type of object and can be used to prove, instead of just Bool
def root_is_nil_or_gt {α : Type} (key: Nat) (tree: MinHeap α): Prop := match tree with
| MinHeap.hnil => True
| MinHeap.hnode k' _ _ _ => k' > key

-- Infered argument is α
def has_heap_property {α: Type} (mh: MinHeap α): Prop := match mh with
| MinHeap.hnil =>
  True
| MinHeap.hnode key _ lt rt =>
  (root_is_nil_or_gt key lt) ∧ (root_is_nil_or_gt key rt) ∧ (has_heap_property lt) ∧ (has_heap_property rt)

def key_in_heap {α: Type} (k: Nat) (mh: MinHeap α) : Prop := match mh with
| MinHeap.hnil =>
  False
| MinHeap.hnode k₁ _ lt rt =>
  (k₁ = k) ∨ (key_in_heap k lt) ∨ (key_in_heap k rt)

def get_root_key_mh {α: Type} (mh: MinHeap α) : (Option Nat) := match mh with
| MinHeap.hnil => none
| MinHeap.hnode k _ _ _ => some k

theorem simple_thm_1 {α: Type} (mh: MinHeap α) (k: Nat) : (((get_root_key_mh mh) = (some k)) → (mh ≠ MinHeap.hnil)) := by
intro h
match mh with
| MinHeap.hnil =>
  contradiction
| MinHeap.hnode k _ lt rt =>
  simp

theorem useful_thm_lt {α: Type} (mh: MinHeap α) (k: Nat) (v: α) (lt: MinHeap α) (rt: MinHeap α) : (has_heap_property mh) → ((mh = (MinHeap.hnode k v lt rt)) → (has_heap_property lt)) := by
intro h₁ h₂
rw [h₂] at h₁
rw [has_heap_property] at h₁
have h₃: (has_heap_property lt) := h₁.right.right.left
exact h₃

theorem useful_thm_rt {α: Type} (mh: MinHeap α) (k: Nat) (v: α) (lt: MinHeap α) (rt: MinHeap α) : (has_heap_property mh) → ((mh = (MinHeap.hnode k v lt rt)) → (has_heap_property rt)) := by
intro h₁ h₂
cases mh with
| hnil => contradiction
| hnode k₁ v₁ lt₁ rt₁ =>
rw[has_heap_property] at h₁
have h₃ := h₁.right.right.right
injection h₂ with h₅ h₆ h₇ h₈
rw[h₈] at h₃
exact h₃

theorem nil_means_no_key {α: Type} (mh: MinHeap α) (k : Nat) : (mh = MinHeap.hnil) → (¬ (key_in_heap k mh)) :=
by
intro h₁
rw[key_in_heap.eq_def]
rw[h₁]
simp

theorem thm_lt_root_key_geq_my_key {α: Type} (mh: MinHeap α) (lt: MinHeap α) (rt: MinHeap α) (v: α) (k: Nat) (k₁: Nat) :
(has_heap_property mh) → (mh = (MinHeap.hnode k v lt rt)) → ((get_root_key_mh lt) = (some k₁)) → (k < k₁) :=
by
intro h₁ h₂ h₃
rw[h₂] at h₁
rw[has_heap_property] at h₁
have h₄ := h₁.left
cases lt with
| hnil => rw[get_root_key_mh] at h₃ ; contradiction
| hnode k₂ v₂ _ _ =>
rw[get_root_key_mh] at h₃
rw[Option.some_inj] at h₃
rw[root_is_nil_or_gt] at h₄
rw[h₃] at h₄
exact h₄

theorem thm_rt_root_key_geq_my_key {α: Type} (mh: MinHeap α) (lt: MinHeap α) (rt: MinHeap α) (v: α) (k: Nat) (k₁: Nat) :
(has_heap_property mh) → (mh = (MinHeap.hnode k v lt rt)) → ((get_root_key_mh rt) = (some k₁)) → (k < k₁) :=
by
intro h₁ h₂ h₃
rw[h₂] at h₁
rw[has_heap_property] at h₁
have h₄ := h₁.right.left
cases rt with
| hnil => rw[get_root_key_mh] at h₃ ; contradiction
| hnode k₂ v₂ _ _ =>
rw[get_root_key_mh] at h₃
rw[Option.some_inj] at h₃
rw[root_is_nil_or_gt] at h₄
rw[h₃] at h₄
exact h₄


theorem root_is_least {α: Type} (mh: MinHeap α) (h_mh: has_heap_property mh) (k: Nat) (k₁: Nat) : ((get_root_key_mh mh) = (some k)) → ((key_in_heap k₁ mh)) → k₁ ≥ k := by
intro h₁ h₂
induction mh generalizing k k₁ with
| hnil =>
  rw [get_root_key_mh] at h₁
  contradiction
| hnode k₂ v₂ lt₂ rt₂ ih_lt ih_rt =>
  rw [get_root_key_mh, Option.some_inj] at h₁
  rw [h₁] at h₂ h_mh
  rw [has_heap_property] at h_mh
  match h_mh with
  | ⟨h₅,⟨ h₆, ⟨ h₇,h₈⟩ ⟩ ⟩ =>
    rw [key_in_heap] at h₂
    cases h₂ with
    | inl h₉ =>
      rw [h₉]
      simp
    | inr h₉ =>
      cases h₉ with
      | inl j₁ => 
        simp
        rw []