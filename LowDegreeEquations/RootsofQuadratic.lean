import Mathlib

def isSolution (a b c x : ℝ) : Prop := a*x^2 + b*x + c = 0

inductive QuadraticSolution (a b c : ℝ) where
|noSolution : (∀ x : ℝ, ¬ isSolution a b c x) → QuadraticSolution a b c
|oneSolution : (x : ℝ) → isSolution a b c x →
  (∀ y : ℝ, isSolution a b c y → y = x) → (QuadraticSolution a b c)
|twoSolution : (x y : ℝ) → isSolution a b c x → isSolution a b c y →
  (∀ z : ℝ, isSolution a b c z → z = x ∨
   z = y) → (QuadraticSolution a b c)

def determinant (a b c : ℝ) : ℝ := b^2 - 4*a*c

lemma QuadHasAtmostTwo (a b c α β γ : ℝ) (hα : isSolution a b c α) (hβ : isSolution a b c β) (hγ : isSolution a b c γ) :  γ = α ∨ γ = β := sorry

noncomputable def solveQuadratic (a b c : ℝ) : QuadraticSolution a b c := 
if determinant a b c > 0 then
  let x := (-b + (determinant a b c)/2)/(2*a)
  let y := (-b - (determinant a b c)/2)/(2*a)
  have hx : isSolution a b c x := by dsimp; sorry
  have hy : isSolution a b c y := sorry

  QuadraticSolution.twoSolution x y 
    hx hy (fun z hz => QuadHasAtmostTwo a b c x y z hx hy hz)
else if determinant a b c = 0 then
  let x := -b/(2*a)
  have hx : isSolution a b c x := sorry
  QuadraticSolution.oneSolution x hx (fun y hy => by cases (QuadHasAtmostTwo a b c x x y hx hx hy) <;> assumption)
else
  QuadraticSolution.noSolution (fun x => sorry) 
