import LowDegreeEquations.Quadratic

namespace QuadRoots

/-
Global variables a b c are defined as real numbers. And a ≠ 0 hypothesis (very important condition for the equation to be quadratic) defined globally.
-/
variable (a b c : ℝ) (a_neq_zero : a ≠ 0)

/-
Define a type to represent the solutions to a quadratic equation-/
def isSolution (x : ℝ) : Prop := a*x^2 + b*x + c = 0

/--We want to solve the quadratic equation ax^2 + bx + c = 0. For that we need to find whether it has no solution (no roots possible), one solution (one unique root, root₁ = root₂), or two solutions (two unique roots, root₁ and root₂). We define a type to represent this. We also define a function to solve the Quadratic equation-/

inductive QuadraticSolution (a b c : ℝ) where
|noSolution : (∀ x : ℝ, ¬ isSolution a b c x) → QuadraticSolution a b c
|oneSolution : (x : ℝ) → isSolution a b c x →
  (∀ y : ℝ, isSolution a b c y → y = x) → (QuadraticSolution a b c)
|twoSolution : (x y : ℝ) → isSolution a b c x → isSolution a b c y →
  (∀ z : ℝ, isSolution a b c z → x≠y → z = x ∨
   z = y) → (QuadraticSolution a b c)

/--We need discriminant to determine whether the quadratic equation has one, two, or no solutions. We define it here-/

def discriminant : ℝ := b^2 - 4*a*c

/--Defining Quadratic Equation in the form of quadratic polynomial-/

noncomputable def p_of_x (x : ℝ) : ℝ := a*x^2 + b*x + c

/--Proving that p_of_x (p(x)) can be factorised into a*(x-α)*(x-β) where α and β are the roots of the quadratic polynomial. Way is assuming there exist q(x) = a*(x-α)*(x-β) such that p(x) - q(x) = a₁*x + a₂ (a₁ a₂:ℝ) and using the fact that p(x) = 0 at α and β, we can prove that p(x) = q(x) at α and β. Hence, p(x) = q(x) for all x-/

lemma p_of_x_factorised (x : ℝ) (h_: p_of_x a b c α=0) (h_': p_of_x a b c β=0) (h: α≠β): p_of_x a b c x = a*(x-α)*(x-β) := by

  let q_of_x ( x:ℝ) := a*(x-α)*(x-β)
  let a₁ := b+α*a+β*a
  let a₂ := c-a*α*β 

  dsimp [p_of_x] at h_; dsimp [p_of_x] at h_'

  have t: p_of_x a b c x - q_of_x x= a₁*x + a₂ :=by
    unfold p_of_x 
    dsimp 
    conv=>
      lhs 
      ring_nf
      rw [add_rotate,←add_assoc,add_sub_assoc',mul_comm]
      rw [mul_rotate,mul_rotate]
      rw [mul_rotate (a:=a),mul_rotate (a:=x)]
      rw [add_right_comm (a:=b*x),add_right_comm (a:=b*x+α*a*x)]
      rw [← distrib_three_right,← add_sub]
    
  have t₁: p_of_x a b c x = q_of_x x + a₁*x + a₂ := by
    simp only [t]
    ring_nf
    simp [mul_comm]
    dsimp [p_of_x]

  have t₂: q_of_x α + a₁*α + a₂ = 0 := by
    simp only [t₁]
    ring_nf
    rw [mul_comm (a:=α)]
    apply h_

  have t₃: q_of_x β + a₁*β + a₂ = 0 := by
    simp only [t₁]
    ring_nf
    rw [mul_comm (a:=β)]
    apply h_'

  have t_: q_of_x α = 0 := by
    dsimp 
    ring_nf

  have t_': q_of_x β = 0 := by
    dsimp 
    ring_nf

  rw [t_] at t₂; rw [t_'] at t₃
  rw [zero_add] at t₂ t₃

  have t₄: a₁ = 0 := by
    by_cases h₂: a₁ = 0
    · assumption
    · rw [←t₃] at t₂
      let t₂' := add_right_cancel t₂
      let t₂'' : a₁⁻¹ * a₁ * α = a₁⁻¹ * a₁ * β   := by
        rw [mul_assoc, mul_assoc, t₂']
      let h₃ := inv_mul_cancel h₂
      rw [h₃, one_mul, one_mul] at t₂''
      contradiction

  have t₅: q_of_x α + a₁*α + a₂ = 0 := by
    simp only [t₁]
    ring_nf
    rw [mul_comm (a:=α)]
    apply h_
    
  have t₆: a₂ = 0 := by
    rw [←t₅]
    rw [t₄,mul_comm,mul_zero,add_zero]
    simp only [t₄]
    ring_nf

  rw [t₄,t₆] at t₁
  rw [mul_comm (a:=0), mul_zero,add_zero,add_zero] at t₁
  exact t₁

/--We need to prove that the Quadratic equation has at most two unique solutions. This is done using factorised form of Quadratic polynomial and if given a third unique solution gamma it can be showed that it has to be either α or β. This is required condition for the QuadraticSolution type. We prove this lemma here-/

lemma QuadHasAtmostTwo (α β γ : ℝ) (hα : isSolution a b c α) (hβ : isSolution a b c β) (hγ : isSolution a b c γ) (h₁': α ≠ β ) :  γ = α ∨ γ = β := by

  have h₁: p_of_x a b c α = 0 := by
    unfold isSolution at hα
    assumption

  have h₂: p_of_x a b c β = 0 := by
    unfold isSolution at hβ
    assumption

  have h₃: p_of_x a b c γ = a*(γ-α)*(γ-β) := by
    apply p_of_x_factorised a b c γ h₁ h₂ h₁'
  
  have h₄: p_of_x a b c γ = 0 := by
    unfold isSolution at hγ
    assumption

  rw [h₃] at h₄

  simp [a_neq_zero] at h₄
  
  have h_': a ≠ 0 := by
    simp [a_neq_zero]
  simp [h_'] at h₄
    
  have h₅: γ = α ∨ γ = β := by
    simp [sub_eq_zero] at h₄
    assumption
  exact h₅
/--This is the function that solves the Quadratic equation. We use the discriminant to determine whether the equation has one, two, or no solutions. If the discriminant is greater than 0, then the equation has two solutions. If the discriminant is equal to 0, then the equation has one solution. If the discriminant is less than 0, then the equation has no solution-/

noncomputable def solveQuadratic : QuadraticSolution a b c := 

if hd: discriminant a b c > 0 then
  let x := (-b + Real.sqrt (discriminant a b c))/(2*a)
  let y := (-b - Real.sqrt (discriminant a b c))/(2*a)
  let h₂':= x≠y 

  have hx : isSolution a b c x := by
    dsimp 
    unfold discriminant
    unfold isSolution
    apply Quadratic.root₁_is_root a b c
    unfold discriminant at hd
    apply le_of_lt hd
    assumption

  have hy : isSolution a b c y := by
    dsimp
    unfold discriminant
    unfold isSolution
    apply Quadratic.root₂_is_root a b c 
    apply le_of_lt hd
    assumption

  QuadraticSolution.twoSolution x y 
    hx hy (fun z hz => QuadHasAtmostTwo a b c a_neq_zero x y z hx hy hz)
  
else if hd': discriminant a b c = 0 then
  let x := -b/(2*a)

  have hx : isSolution a b c x := by
    dsimp
    simp [discriminant] at hd'
    unfold isSolution

    have ld : a * (-b / ((2 : ℝ) * a)) ^ 2 + b * (-b / ((2: ℝ) * a)) + c = (b^2 - (4: ℝ) * a * c) / ((4: ℝ) * a) := by 
      conv=>
        lhs
        simp [neg_sq]
        ring_nf
      sorry
    
    rw [ld]
    rw [hd']
    simp [mul_zero]
  
  QuadraticSolution.oneSolution x hx (fun y hy => by sorry)

else
  QuadraticSolution.noSolution (fun x => by
    by_cases h: a > 0
    · sorry

    · sorry)

end QuadRoots