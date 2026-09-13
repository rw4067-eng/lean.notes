import Mathlib

--- goal := a ≠ b
--- goal := (a = b) → False
lemma helper (a b : ℕ → Bool) (n : ℕ) (wit : a n ≠ b n) : a ≠ b := by
  intro h
  apply wit
  exact (congrFun h n)

lemma helper_term (a b : ℕ → Bool) (n : ℕ) (wit : a n ≠ b n) : a ≠ b :=
  fun h ↦
  by exact wit (congrFun h n)

theorem cantor_diagonalization (family : ℕ → (ℕ → Bool)) :
    ∃ diagonal : ℕ → Bool, ∀ n, diagonal ≠ family n := by
  use fun n : ℕ ↦ !family n n -- diagonal (g)
  intro m
  apply helper_term (fun n : ℕ ↦ !family n n) (family m) m
  exact Bool.not_not_eq.mpr rfl

theorem cantor_diagonalization_term (family : ℕ → (ℕ → Bool)) :
    ∃ diagonal : ℕ → Bool, ∀ n, diagonal ≠ family n := ⟨ fun n : ℕ ↦ !family n n ,
            fun _ : ℕ ↦ helper_term _ _ _ (Bool.not_not_eq.mpr rfl) ⟩



def do_twice (α: Type) (f : α → α) : α → α := fun x : α ↦ f (f x)

def square (n : ℕ) : ℕ := n * n

#eval do_twice ℕ square 2

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := fun x y ↦ f (x, y)
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := fun (x, y) ↦ f x y
