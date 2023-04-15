import Mathlib

def isSolution (a b c x : ℝ) : Prop := a*x^2 + b*x + c = 0

inductive QuadraticSolution (a b c : ℝ) where
|noSolution : (∀ x : ℝ, ¬ isSolution a b c x) → QuadraticSolution a b c
|oneSolution : (x : ℝ) → isSolution a b c x →
  (∀ y : ℝ, isSolution a b c y → y = x) → (QuadraticSolution a b c)
|twoSolution : (x y : ℝ) → isSolution a b c x → isSolution a b c y →
  (∀ z : ℝ, isSolution a b c z → z = x ∨
   z = y) → (QuadraticSolution a b c)
