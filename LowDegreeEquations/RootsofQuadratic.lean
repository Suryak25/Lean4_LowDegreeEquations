import Mathlib

/-
Define a type to represent the solutions to a quadratic equation.
-/
def isSolution (a b c x : ℝ) : Prop := a*x^2 + b*x + c = 0

/-
We want to solve the quadratic equation ax^2 + bx + c = 0. For that we need to find whether it has no solution (no roots possible), one solution (one unique root, root₁ = root₂), or two solutions (two unique roots, root₁ and root₂). We define a type to represent this. We also define a function to solve the Quadratic equation.
-/
inductive QuadraticSolution (a b c : ℝ) where
|noSolution : (∀ x : ℝ, ¬ isSolution a b c x) → QuadraticSolution a b c
|oneSolution : (x : ℝ) → isSolution a b c x →
  (∀ y : ℝ, isSolution a b c y → y = x) → (QuadraticSolution a b c)
|twoSolution : (x y : ℝ) → isSolution a b c x → isSolution a b c y →
  (∀ z : ℝ, isSolution a b c z → z = x ∨
   z = y) → (QuadraticSolution a b c)

/-
We need discriminant to determine whether the quadratic equation has one, two, or no solutions. We define it here.
-/
def discriminant (a b c : ℝ) : ℝ := b^2 - 4*a*c

/-
We need to prove that the Quadratic equation has at most two unique solutions. Hence, we need to prove that if the Quadratic equation has three solutions, then two of the three solutions are the same. This is required condition for the QuadraticSolution type. We prove this lemma here.
-/
lemma QuadHasAtmostTwo (a b c α β γ : ℝ) (hα : isSolution a b c α) (hβ : isSolution a b c β) (hγ : isSolution a b c γ) :  γ = α ∨ γ = β := by
  unfold isSolution at hα hβ hγ
  
  sorry

/-
This is the function that solves the Quadratic equation. We use the discriminant to determine whether the equation has one, two, or no solutions. If the discriminant is greater than 0, then the equation has two solutions. If the discriminant is equal to 0, then the equation has one solution. If the discriminant is less than 0, then the equation has no solution.
-/
noncomputable def solveQuadratic (a b c : ℝ) : QuadraticSolution a b c := 
if discriminant a b c > 0 then
  let x := (-b + (discriminant a b c)/2)/(2*a)
  let y := (-b - (discriminant a b c)/2)/(2*a)
  have hx : isSolution a b c x := by dsimp; sorry
  have hy : isSolution a b c y := sorry

  QuadraticSolution.twoSolution x y 
    hx hy (fun z hz => QuadHasAtmostTwo a b c x y z hx hy hz)
else if discriminant a b c = 0 then
  let x := -b/(2*a)
  have hx : isSolution a b c x := sorry
  QuadraticSolution.oneSolution x hx (fun y hy => by cases (QuadHasAtmostTwo a b c x x y hx hx hy) <;> assumption)
else
  QuadraticSolution.noSolution (fun x => sorry) 
