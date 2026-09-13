
import Mathlib
example (P Q : Prop) : P → Q → P := by
  intro p
  intro q
  exact p
  -- you fill this

example (P Q : Prop) : P ∧ Q → P := by
  intro hpq
  exact hpq.1


  -- you fill this

example : ∃ x : ℝ, x + 1 = 3 := by
  use 2
  norm_num
  -- you fill this

example (f : ℝ → ℝ) (h : ∀ x, f x = x^2) : f 3 = 9 := by
  rw[h]
  norm_num

example (P Q : Prop) : P → (P → Q) → Q := by
  intro hp
  intro hpq
  apply hpq
  exact hp


example (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro hpq
  intro hqr
  intro hp
  apply hqr
  apply hpq
  apply hp

example (P Q R : Prop) : (P ∧ Q) → (P → R) → R := by
  intro hpq
  intro hpr
  apply hpr
  exact hpq.1

example (P Q R : Prop) : (P → Q) → (P → R) → P → (Q ∧ R) := by
  intro hpq
  intro hpr
  intro hp
  exact ⟨hpq hp, hpr hp⟩

example (P Q R : Prop) : (P → Q) → (P → R) → P → (Q ∧ R) := by
  intro hpq
  intro hpr
  intro hp
  constructor
  apply hpq
  exact hp
  apply hpr
  exact hp

example (P Q R : Prop) : (P ∧ Q) → (Q → R) → (R ∧ P) := by
  intro hpq
  intro hqr
  constructor
  apply hqr
  exact hpq.2
  exact hpq.1

example (P Q R : Prop) : (P → Q ∧ R) → P → Q := by
 intro hpqr
 intro hp
 exact (hpqr hp).1

example (P Q R : Prop) : (P → Q) → (Q → R) → (P ∧ Q) → (Q ∧ R) := by
  intro hpq
  intro hqr
  intro hpq1
  constructor
  exact (hpq hpq1.1)
  exact (hqr hpq1.2)
