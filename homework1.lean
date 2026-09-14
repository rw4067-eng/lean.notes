import Mathlib

section Continuous

/-!
# Homework 1: Continuity

The goal of this week's homework is to prove the following result:
the sum of two continuous functions from ℝ to ℝ is continuous.
-/

/-!
## 1. Metric spaces

We will structure the proof in a reusable way. Lean lets you state that a
space comes with a distance (a metric). We do this by requiring a
`MetricSpace X` instance.
-/

variable {X : Type} [MetricSpace X]

-- Metric spaces come with the usual functions and facts.
#check dist           -- The distance function `X → X → ℝ`.
#check dist_triangle  -- The triangle inequality.
#check dist_eq_zero   -- The fact that `dist a b = 0 ↔ a = b`.

-- We define another metric space `Y` so that we can talk about continuous
-- functions between metric spaces.
variable {Y : Type} [MetricSpace Y]

/-!
## 2. The definition of continuity

Your first goal is to define continuity at a point for metric spaces.
-/

def Continuous_at (x : X) (f : X → Y) : Prop :=
∀ ε, ε > 0 →  ∃ δ, δ >0 ∧ ( ∀ z : X,  dist x z < δ → dist (f x)  (f z) < ε)
-- Extend the definition to globally continuous functions. We call it
-- `Continuous'` because Lean already has a definition named `Continuous`.

def Continuous' (f : X → Y) : Prop :=
∀ x : X, Continuous_at x f

/-!
## 3. Composition of continuous functions

Our first proof goal is that a composition of continuous functions is
continuous. To prove this:

1. State and prove a pointwise version named `Comp_Continuous_at`.
2. Use the pointwise version to prove `Comp_Continuous`.
-/

variable {Z : Type} [MetricSpace Z]
variable {T : Type} [MetricSpace T]

/-!
## 4. Composition of continuous functions: metric-space version
-/

def h (f : X → Y) (g: Y → Z): X → Z:= g∘ f
def Comp_Continuous_at (x: X) (f: X → Y) (g : Y → Z):=
Continuous_at x (h f g)

theorem Comp_Continuous_at'
    (x : X) (f : X → Y) (g : Y → Z)
    (hf : Continuous_at x f)
    (hg : Continuous_at (f x) g) :
    Comp_Continuous_at x f g := by
    show ∀ ε, ε > 0 →
    ∃ δ, δ > 0 ∧
    ∀ z : X,
      dist x z < δ →
      dist ((h f g) x) ((h f g) z) < ε
    intro ε
    intro hε
    have hgε := hg ε hε
    rcases hgε with ⟨δg, δg1,hg1⟩
    have hfδg := hf δg δg1
    rcases hfδg with ⟨ δf, δf1, hf1⟩
    use δf
    constructor
    exact δf1
    intro z
    intro hz
    have hfz := hf1 z hz
    have hgz := hg1 (f z) hfz
    exact hgz







theorem Comp_Continuous (f : X → Y) (g : Y → Z)
    (hf : Continuous' f) (hg : Continuous' g) :

    Continuous' (h f g) := by
      show ∀ x :X, Comp_Continuous_at x f g
      intro x
      apply Comp_Continuous_at' x f g
      exact hf x
      exact hg (f x)


/-!
## 5. Some plumbing for continuous functions

Lean is pretty smart, and we can use it to register mathematical facts
automatically. In this case, Mathlib has already registered that a product of
metric spaces is a metric space, with
`dist (a, b) (c, d) = max (dist a c) (dist b d)`.
This is recorded as follows:
-/

#check Prod.dist_eq

-- Define the Cartesian product of two functions as a map from the product of
-- the input spaces to the product of the output spaces.
def FProd (f : X → Y) (g : Z → T) : X × Z → Y × T :=
  fun (x, z) ↦ (f x, g z)

-- Prove that the Cartesian product of functions continuous at the respective
-- input points is continuous at the corresponding pair.
theorem Prod_Continuous_at (x : X) (z : Z) (f : X → Y) (g : Z → T)
    (hf : Continuous_at x f) (hg : Continuous_at z g) :
    Continuous_at (x, z) (FProd f g) := by
     show ∀ ε , ε >0 → ∃ δ, δ>0 ∧
     ∀ p : X × Z,
       dist (x , z) p < δ
       → dist ((FProd f g ) (x,z)) ( (FProd f g) p) <ε
     intro ε
     intro hε
     have hfε := hf ε hε
     rcases hfε with ⟨ δf, δf1, hf1 ⟩
     have hgε := hg ε hε
     rcases hgε with ⟨ δg, δg1, hg1 ⟩
     use  min δf δg
     constructor
     exact lt_min δf1 δg1
     intro p
     rcases p with ⟨x1, z1 ⟩
     intro hfg
     show max (dist (f x) (f x1)) (dist (g z) (g z1))< ε
     rw [max_lt_iff]
     constructor
     apply hf1
     rw [Prod.dist_eq] at hfg
     simp at hfg
     rcases hfg with ⟨hfg1,hfg2,hfg3⟩
     exact hfg1.1
     apply hg1
     rw [Prod.dist_eq] at hfg
     simp at hfg
     rcases hfg with ⟨hfg1,hfg2,hfg3⟩
     exact hfg3






-- Write the global `Prod_Continuous` version as well.
theorem Prod_Continuous (f : X → Y) (g: Z → T)
(hf : Continuous' f) (hg : Continuous' g) :
Continuous' (FProd f g) := by
  show ∀ p : X × Z, Continuous_at p (FProd f g)
  intro p
  rcases p with ⟨ x, z ⟩
  apply Prod_Continuous_at x z f g
  exact hf x
  exact hg z


variable {A : Type} [MetricSpace A]
-- Do the same for the diagonal map.
def Diag (A : Type) : A → A × A :=
  fun a ↦ (a, a)


-- Write the pointwise and global continuity results for `Diag`.
theorem Continuous_Diag_at (a: A) :
Continuous_at a (fun a ↦ (a, a)) := by
  show ∀ ε, ε>0 → ∃ δ, δ>0 ∧ ∀ b: A , dist a b <δ
  → dist ((Diag A) a)  ((Diag A) b) < ε
  intro ε
  intro hε
  use ε
  constructor
  exact hε
  intro b
  intro hab
  show dist (a,a) (b,b) < ε
  rw [Prod.dist_eq]
  simp
  exact hab



theorem Continuous_Diag : Continuous' (Diag A) := by
  show ∀ a : A , Continuous_at a (Diag A)
  intro a
  exact Continuous_Diag_at a


/-!
## 6. Addition is continuous

This is a `calc` block. If you have never seen this proof before, one hint:
using `δ = ε / 3` makes it slightly easier (although `ε / 2` should work).
-/

def add : ℝ × ℝ  → ℝ := fun (a,b) ↦  a+b
theorem R_add_continuous_at (v : ℝ × ℝ) :
    Continuous_at v (fun (a, b) ↦ a + b) := by
    show Continuous_at v add
    show ∀ ε, ε >0 → ∃ δ, δ >0 ∧
    ∀ u : ℝ × ℝ , (dist v u) <δ → dist (add v) (add u) < ε
    intro ε
    intro hε
    use ε/3
    constructor
    positivity
    rcases v with ⟨a,b⟩
    intro u
    rcases u with ⟨c,d ⟩
    intro habcd
    show dist (a+b) (c+d) < ε
    rw [Prod.dist_eq] at habcd
    simp at habcd
    rcases habcd with ⟨h1, h2 ⟩
    have hadd : dist (a + b) (c + d) ≤ dist a c + dist b d := by
     calc
      dist (a + b) (c + d)
      ≤ dist (a + b) (c + b) + dist (c + b) (c + d) := by
             exact dist_triangle (a+b) (c+b) (c+d)
      _= dist a c + dist b d := by
            simp [dist_add_right, dist_add_left]
    suffices hsum: dist a c + dist b d < ε  by
      exact lt_of_le_of_lt hadd hsum
    calc
      dist a c + dist b d
      <  ε/3 + dist b d := by
        exact (add_lt_add_iff_right (dist b d)).mpr h1
      _ < ε /3 + ε/3 := by
          exact add_lt_add_right h2 (ε / 3)
    linarith





-- Write the global `R_add_continuous` version as well.

theorem R_add_continuous : Continuous' add := by
  show ∀ v : ℝ × ℝ, Continuous_at v add
  intro v
  exact R_add_continuous_at v



/-!
## 7. Addition of continuous functions

Look at the theorems you have proved. If we denote the product by `(f, g)`
and addition by `+`, then

`f + g = (+) ∘ (f, g) ∘ Δ`.

You only have to combine the previous results.
-/

theorem add_cont (f g : ℝ → ℝ)
    (hf : Continuous' f)
    (hg : Continuous' g) :
    Continuous' (f + g) := by
      have hfg : f + g
      = add ∘ (FProd f g) ∘ (Diag ℝ) := by
        funext x
        simp [add, FProd, Diag]
      rw [hfg]
      have hdiag: Continuous' (Diag ℝ) := by
        exact Continuous_Diag
      have hprod: Continuous' (FProd f g):= by
        apply Prod_Continuous f g
        exact hf
        exact hg
      have hinner:
      Continuous' ((FProd f g) ∘ (Diag ℝ)) := by
        apply Comp_Continuous  (Diag ℝ) (FProd f g)
        exact hdiag
        exact hprod
      apply Comp_Continuous  ((FProd f g) ∘ (Diag ℝ)) (add)
      exact hinner
      exact R_add_continuous






end Continuous
