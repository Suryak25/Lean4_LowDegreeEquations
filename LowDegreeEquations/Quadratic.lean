import Mathlib

namespace Quadratic

/-Defining the two roots of quadratic equation-/
noncomputable def root₁ (a b c : ℝ) : ℝ :=
(-b + Real.sqrt (b^2 - 4*a*c)) / (2*a)

/-Defining the two roots of quadratic equation-/
noncomputable def root₂(a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0): ℝ :=
(-b - Real.sqrt (b^2 - 4*a*c)) / (2*a) 

def two_mul_two (R : Type) [Ring R] : (4: R) = (2 : R) * (2: R) := by /-proof that 2(ℝ) * 2(ℝ) = 4(ℝ) -/
    have : (2: R) = (1: R) + (1: R) := by norm_cast
    rw [this, mul_add, mul_one]
    norm_cast
/-- Simplifying the term with power 1 of the root₁.
The simplification in RHS is done by hand (Expected).
In LHS theorems are used to simplify into the expected term.
For this lemma h' is required as there is a stage in simplification where 2*a is multiplied and divided, hence proved that given h', 2*a ≠ 0 -/
private lemma l₁ (a b c : ℝ) (h': a≠0): (b * ((-b + Real.sqrt (b * b - 4*a*c)) / (2 * a))) = ((-(2*a*b*b)/(4*a*a)) + ((2*a*b*(Real.sqrt (b * b - 4*a*c)))/(4*a*a))) := by

  have h' : 2*a ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, h', or_self, not_false_iff] 
  conv=>
    lhs
    simp only [add_div,mul_div,mul_add, add_mul]
    rw [←mul_div_mul_right (c:=2*a) (hc:=h')] /-divide and multiply by 2*a -/
    rw [←mul_div_mul_right (c:=2*a) (a:=b * Real.sqrt (b * b - 4 * a * c)) (b := 2*a) (hc:=h')] /-divide and multiply by 2*a -/
    simp [mul_left_comm (a:=b) (b:=2) (c:=a)]
    rw [mul_left_comm,mul_right_comm,mul_assoc]
    rw [←mul_left_comm (a:=a) (b:=b) (c:=b)]
    rw [mul_mul_mul_comm]
    rw [mul_rotate (a:=b) (b:=(Real.sqrt (b * b - 4 * a * c))) (c:=2*a)]
    rw [mul_rotate (a:=Real.sqrt (b * b - 4 * a * c)) (b:=2*a) (c:=b)]
    simp only [←mul_assoc]
    simp [←two_mul_two]

/--Simplifying the term with power 2 of root₁.
The simplification RHS is the expected simplification (done by hand). 
So, using theorems and ring tactic (on LHS) it is proved that the term actually reduces to hand simplified term-/

private lemma l₂ (a b c : ℝ) (h:0 ≤ (b*b - 4*a*c)):
  a *((-b * -b + Real.sqrt (b * b - 4 * a * c) * -b +
        (-b * Real.sqrt (b * b - 4 * a * c) +
          Real.sqrt (b * b - 4 * a * c) * Real.sqrt (b * b - 4 * a * c))) /
              (2 * (2 * a * a))) = 
                (2*a*b*b - 4*a*a*c - 2*a*b*Real.sqrt (b*b - 4*a*c))/(4*a*a) := by
                conv=>
                  lhs
                  rw [Real.mul_self_sqrt h]
                  simp only [mul_div,mul_add,mul_sub]
                  simp only [←mul_assoc]
                  simp [←two_mul_two]
                  rw [mul_right_comm (a:=a) (b:=Real.sqrt (b*b - 4*a*c) ) (c:=b)]
                  rw [←add_assoc]
                ring

/-- Proof that root₁ is actually the root of quadratic.
Essentially it is simplification using various theorems, and split into major 3 terms out of which two are bigger terms
and are simplified in private lemmas l₁ (specifically pass h:= a ≠ 0 as it involves multiplication and addition of 2*a) and l₂.
Once the major 2 terms are simplified, its rewritten and then ring_nf tactic is applied along with some more simplification theorems-/

theorem root₁_is_root (a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0) (h': a≠0): a*(root₁ a b c)^2 + b*(root₁ a b c) + c = 0 := by
  simp only [root₁, div_pow]
  simp only [pow_two, mul_left_comm, mul_add, add_mul] at h ⊢
  rw [l₁ (h':=h')]
  rw [l₂]
  ring_nf
  simp only [pow_two]
  simp [←mul_rotate (a:=a⁻¹*a⁻¹) (b:=a*a) (c:=c)]
  rw [mul_mul_mul_comm]
  rw[←one_div]
  rw [one_div_mul_cancel (h:=h')]
  rw [mul_one,one_mul]
  rw [neg_add_self]
  assumption

/-- Simplifying term with power 1 of root₂.
The RHS is expected simplification (Done by hand).
LHS indeed gets simplified to the expected term.
This lemma requires h' and also proof that 2*a ≠ 0, as it is being multiplied and divided by 2*a -/

private lemma l'₁ (a b c : ℝ) (h:(b*b - 4*a*c) ≥ 0) (h': a≠0): (b * ((-b - Real.sqrt (b * b - 4*a*c)) / (2 * a))) = ((-(2*a*b*b)/(4*a*a)) - ((2*a*b*(Real.sqrt (b * b - 4*a*c)))/(4*a*a))) := by

  have h' : 2*a ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, h', or_self, not_false_iff] 
  conv=>
    lhs
    simp only [sub_div,mul_div,mul_sub, add_mul]
    rw [←mul_div_mul_right (c:=2*a) (hc:=h')] /-divide and multiply by 2*a -/
    rw [←mul_div_mul_right (c:=2*a) (a:=b * Real.sqrt (b * b - 4 * a * c)) (b := 2*a) (hc:=h')] /-divide and multiply by 2*a -/  
    simp [mul_left_comm (a:=b) (b:=2) (c:=a)]
    rw [mul_left_comm,mul_right_comm,mul_assoc]
    rw [←mul_left_comm (a:=a) (b:=b) (c:=b)]
    rw [mul_mul_mul_comm]
    rw [mul_rotate (a:=b) (b:=(Real.sqrt (b * b - 4 * a * c))) (c:=2*a)]
    rw [mul_rotate (a:=Real.sqrt (b * b - 4 * a * c)) (b:=2*a) (c:=b)]
    simp only [←mul_assoc]
    simp [←two_mul_two]

/-- Simplifying term with power 2 of root₂.
The RHS is the expected hand simplified term.
The LHS gets simplified to expected term-/

private lemma l'₂ (a b c : ℝ) (h:(b*b - 4*a*c) ≥ 0): 
  a *((-b * -b - Real.sqrt (b * b - 4 * a * c) * -b -
          (-b * Real.sqrt (b * b - 4 * a * c) -
            Real.sqrt (b * b - 4 * a * c) * Real.sqrt (b * b - 4 * a * c))) /
                (2 * (2 * a * a))) = 
                  (2*a*b*b - 4*a*a*c + 2*a*b*Real.sqrt (b*b - 4*a*c))/(4*a*a) := by
                    conv=>  
                      lhs
                      rw [Real.mul_self_sqrt h]
                      simp only [mul_div,mul_add,mul_sub]
                      simp only [←mul_assoc]
                      simp [←two_mul_two]
                      rw [sub_eq_add_neg]
                      rw [neg_sub]
                      rw [sub_neg_eq_add]
                      rw [←add_assoc]
                      rw [add_rotate]
                      rw [add_rotate']
                      rw [add_rotate']
                      simp [←add_assoc]
                      rw [add_assoc]
                      rw[add_add_add_comm]
                      rw [← mul_rotate]
                      rw[mul_comm b a]
                      rw [←mul_two (n :=a * b * Real.sqrt (b * b - 4 * a * c))]
                      rw [sub_eq_add_neg (a * b * b)]
                      rw [← add_rotate]
                      rw [← mul_two]
                      rw [add_rotate']
                      rw[←add_assoc]
                      rw [←sub_eq_add_neg]
                      rw [mul_rotate (a:=a) (b:=4) (c:=a)]
                      rw [mul_rotate]
                      rw [mul_comm b 2,mul_mul_mul_comm]
                      rw [←mul_assoc]
                      rw [mul_comm (a * b * (Real.sqrt (b * b - 4 * a * c))) 2]
                      rw [←mul_assoc]
                      rw [←mul_assoc]

/-- Proof that root₂ is actually the root of quadratic.
Essentially it is simplification using various theorems, and split into major 3 terms out of which two are bigger terms
and are simplified in private lemmas l'₁ (specifically pass h:= a ≠ 0 as it involves multiplication and addition of 2*a) and l'₂.
Once the major 2 terms are simplified, its rewritten and then ring_nf tactic is applied along with some more simplification theorems-/

theorem root₂_is_root (a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0) (h': a≠0): a*(root₂ a b c h)^2 + b*(root₂ a b c h) + c = 0 := by
  simp only [root₂, div_pow]
  simp only [pow_two, mul_left_comm, mul_sub, sub_mul] at h ⊢
  rw [l'₁ (h':=h')]
  rw [l'₂]
  ring_nf
  simp only [pow_two]
  simp [←mul_rotate (a:=a⁻¹*a⁻¹) (b:=a*a) (c:=c)]
  rw [mul_mul_mul_comm]
  rw[←one_div]
  rw [one_div_mul_cancel (h:=h')]
  rw [mul_one,one_mul]
  rw [neg_add_self]
  assumption
  assumption

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
  (∀ z : ℝ, isSolution a b c z → x≠y → z = x ∨
   z = y) → (QuadraticSolution a b c)

/-
We need discriminant to determine whether the quadratic equation has one, two, or no solutions. We define it here.
-/
def discriminant (a b c : ℝ) : ℝ := b^2 - 4*a*c

/-
Defining Quadratic Equation in the form of quadratic polynomial.
-/
noncomputable def p_of_x (a b c x : ℝ) : ℝ := a*x^2 + b*x + c

/-
Proving that p_of_x (p(x)) can be factorised into a*(x-α)*(x-β) where α and β are the roots of the quadratic polynomial. Way is assuming there exist q(x) = a*(x-α)*(x-β) such that p(x) - q(x) = a₁*x + a₂ (a₁ a₂:ℝ) and using the fact that p(x) = 0 at α and β, we can prove that p(x) = q(x) at α and β. Hence, p(x) = q(x) for all x.
-/
lemma p_of_x_factorised (a α β x : ℝ) (h_: p_of_x a b c α=0) (h_': p_of_x a b c β=0) (h: α≠β): p_of_x a b c x = a*(x-α)*(x-β) := by
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
    rw [←t₃] at t₂ 
    simp [add_right_cancel (a:=a₁*α) (b:=a₂) (c:=a₁*β)] at t₂  
    by_cases t₂: α = β
    · contradiction
    · sorry

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
/-
We need to prove that the Quadratic equation has at most two unique solutions. This is done using factorised form of Quadratic polynomial and if given a third unique solution gamma it can be showed that it has to be either α or β. This is required condition for the QuadraticSolution type. We prove this lemma here.
-/
lemma QuadHasAtmostTwo (a b c α β γ : ℝ) (hα : isSolution a b c α) (hβ : isSolution a b c β) (hγ : isSolution a b c γ) (h₁': α ≠ β ) :  γ = α ∨ γ = β := by
  have h₁: p_of_x a b c α = 0 := by
    unfold isSolution at hα
    assumption
  have h₂: p_of_x a b c β = 0 := by
    unfold isSolution at hβ
    assumption
  have h₃: p_of_x a b c γ = a*(γ-α)*(γ-β) := by
    unfold p_of_x_factorised a α β γ h₁ h₂ h₁'
    assumption
    
  -- have h₃: = 0 := by
  --   unfold p_of_x_factorised a α β γ at 

  
  sorry
/-
This is the function that solves the Quadratic equation. We use the discriminant to determine whether the equation has one, two, or no solutions. If the discriminant is greater than 0, then the equation has two solutions. If the discriminant is equal to 0, then the equation has one solution. If the discriminant is less than 0, then the equation has no solution.
-/
noncomputable def solveQuadratic (a b c : ℝ) (h₁: a≠0 ) : QuadraticSolution a b c := 

if hd: discriminant a b c > 0 then
  let x := (-b + Real.sqrt (discriminant a b c))/(2*a)
  let y := (-b - Real.sqrt (discriminant a b c))/(2*a)
  let h₂':= x≠y 

  have hx : isSolution a b c x := by
    dsimp 
    unfold discriminant
    unfold isSolution
    apply root₁_is_root a b c
    unfold discriminant at hd
    apply le_of_lt hd
    assumption

  have hy : isSolution a b c y := by
    dsimp
    unfold discriminant
    unfold isSolution
    apply root₂_is_root a b c 
    apply le_of_lt hd
    assumption

  QuadraticSolution.twoSolution x y 
    hx hy (fun z hz => QuadHasAtmostTwo a b c x y z hx hy hz)
  
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
        -- simp [pow_two]
        -- rw [←mul_assoc,mul_rotate]
        -- rw [mul_assoc]
        -- simp [div_mul_comm]
        -- rw [← div_one (a:=c)]
        -- rw [← mul_div_mul_right (a:=c) (c:=4*a) (hc:=h₁),←mul_assoc (a:=1)]
        -- rw [←mul_assoc (a:=c),mul_rotate]
        -- rw[mul_rotate (a:=1),mul_one]
        -- simp [mul_div] 
        -- rw [← mul_assoc (a:=-b/(2*a))]
        -- rw [div_mul_div_comm]
        -- rw [mul_mul_mul_comm]
        -- simp [← two_mul_two,← mul_assoc]
        -- rw [← mul_div_mul_right (a:=-(b*b)) (c:=2),← mul_comm]
        -- rw [mul_rotate (a:=2), mul_rotate (a:=a),←two_mul_two]
        -- ring_nf
        -- rw [pow_two (a:=a⁻¹),pow_two,← mul_assoc]
        -- ring
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

end Quadratic