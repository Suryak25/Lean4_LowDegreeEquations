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

  simp only [mul_eq_zero, a_neq_zero, false_or] at h₄
  
  simp only at h₄
    
  have h₅: γ = α ∨ γ = β := by
    simp only [sub_eq_zero] at h₄
    assumption
  exact h₅

/--To perform simplifications in the discriminant = 0 case part of solveQuadratic
-/
private lemma le: b*(-b/(2*a)) = -(b*b)/(2*a) := by
  simp only [mul_neg, mul_div, neg_div]    

private lemma le': a*(b*b/(a * a * 4)) = b*b/(4*a) := by
  rw [mul_div,← mul_assoc,mul_rotate]
  conv=>
    lhs
    rw [←mul_rotate (a:=4),mul_div_mul_right (c:=a) (hc:=a_neq_zero)]

private lemma le_: a * b / (2 * a) = b / 2 := by
  simp only [mul_div, mul_comm,mul_div_mul_left (c:=a) (hc:=a_neq_zero)]

private lemma le₁: b / 2 * b / (2 * a) = b * b / (4 * a) := by
  simp only [mul_div, mul_comm]
  rw [←mul_one (a:=2),←mul_assoc,mul_rotate,mul_rotate,one_mul,mul_comm (a:=a)]
  simp only [mul_one, div_div, mul_assoc, Quadratic.two_mul_two]
  simp only [mul_comm,mul_rotate']

private lemma le₂: a * y * b / (2 * a) = b/2 * y := by
  conv=>
    lhs
    rw [mul_comm (a:=a),mul_assoc,←mul_div,mul_comm]
    rw [mul_comm (a:=a),mul_div_mul_right (c:=a) (hc:=a_neq_zero)]

private lemma le_': 2*(b/2) = b := by
  simp [mul_div, mul_comm]

private lemma le_'': a*y*y = a*y^2:=by
  conv=>
    lhs
    rw [mul_rotate,←pow_two,mul_comm]

private lemma le_''': b * y + a * y ^ 2 = a * y ^ 2 + b * y := by
  rw [←add_comm (a:=b*y)]

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
    simp [discriminant,pow_two] at hd'
    have hd': b*b = 4*a*c:= by
      simp [sub_eq_iff_eq_add] at hd'
      assumption

    unfold isSolution

    have hc: 4*a ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, a_neq_zero, or_self, not_false_iff]
    have hc': (2 : ℝ)  ≠ 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_iff]

    simp only [div_pow,neg_sq]
    simp only [pow_two, mul_assoc, mul_comm, mul_left_comm]
    rw [←mul_assoc]
    simp only [← Quadratic.two_mul_two]
    rw [add_rotate,mul_comm (a:=a)]
    rw [le]
    rw [← mul_div_mul_right (a:=-(b*b)) (c:=2) (hc:=hc'),←div_one (a:=c)]
    rw [← mul_div_mul_right (a:=c) (c:=4*a) (hc:=hc),←mul_assoc,←mul_assoc,mul_rotate (a:=1),mul_one, mul_rotate, mul_rotate,← Quadratic.two_mul_two]
    rw [le',mul_rotate]
    simp only [neg_mul]
    simp [←add_div]
    rw [←hd',add_rotate,←mul_two]
    simp only [add_right_neg, true_or]
    assumption
  
  QuadraticSolution.oneSolution x hx (fun y hy => by 
  simp only [discriminant] at hd'
  unfold isSolution at hy; unfold isSolution at hx
  
  have hc: 4*a ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, a_neq_zero, or_self, not_false_iff]
  have hc': (2 : ℝ)  ≠ 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_iff]
  
  have h_: b^2/(4*a) - c = 0 := by
    rw [←div_one (a:=c),←mul_div_mul_right (a:=c) (c:=4*a) (hc:=hc),←mul_assoc,←mul_assoc,mul_rotate (a:=1),mul_one]
    rw [mul_rotate,←sub_div]
    simp only [div_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    simp only [a_neq_zero,or_false]
    assumption
  
  have h₁: b^2/(4*a) = c:= by
    simp only [sub_eq_iff_eq_add,zero_add] at h_
    assumption

  rw [←h₁] at hy
  rw [←hy] at hx

  have h₂: a*(y + (b/(2*a)))^2 = a * y ^ 2 + b * y + b ^ 2 / (4 * a):= by
    simp only [pow_two,←mul_assoc]
    simp only [mul_add]
    simp only [add_mul,mul_div,add_div]
    rw [le_,le₁,le₂,←add_assoc,add_rotate (a:=a*y*y),←mul_two]
    rw [mul_rotate (a:=b/2),mul_rotate (a:=y),le_',le_'',←pow_two]
    rw [le_''']  
    assumption
    assumption  

  simp only [hy, mul_eq_zero, zero_lt_two, pow_eq_zero_iff] at h₂
  simp only [a_neq_zero, false_or] at h₂

  have h₃: y = -b/(2*a) := by
    have l : y + b/(2 * a) = - b/(2*a) + b/(2*a) := by
      rw [h₂]
      rw [add_comm]
      simp only [neg_div, add_right_neg]
    rw [add_right_cancel l]
  
  assumption)

else
  QuadraticSolution.noSolution (fun y => by
    intro h_
    unfold isSolution at h_

    have hc: 4*a ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, a_neq_zero, or_self, not_false_iff]
    have hc': (4 : ℝ)  ≠ 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_iff]
    
    by_cases h: a > 0
    · have h₁: discriminant a b c < 0 := by
        let trich:= lt_trichotomy (discriminant a b c) 0
        cases trich
        case inl _ => assumption
        case inr h => simp [hd,hd'] at h
      
      unfold discriminant at h₁

      have h₃: b^2/(4*a) - c < 0 := by
        let h' := inv_pos.2 h
        let h₁' := mul_lt_mul_of_pos_right h₁ h'
        rw [zero_mul,sub_mul] at h₁'

        simp only [inv_eq_one_div] at h₁'
        rw [mul_comm (a:=4*a),mul_rotate,←mul_mul_div] at h₁'
        rw [mul_div,mul_one] at h₁'
        
        have hc_: 0 < (1/4:ℝ)  := by
          have v': (4 : ℝ)⁻¹ > 0 := by simp
          simp only [one_div, inv_pos.2, zero_lt_four]
          
        let v := mul_lt_mul_of_pos_right h₁' hc_ 
        rw [zero_mul,sub_mul,←mul_rotate,div_mul_div_comm,mul_one,one_div_mul_cancel,one_mul,mul_comm] at v
        exact v
        exact hc'
        exact a_neq_zero

      have h₄: a * y ^ 2 + b * y + b^2/(4*a) < 0 := by
        
        sorry
      have h₅: a*(y + (b/(2*a)))^2 = a * y ^ 2 + b * y + b^2/(4*a) := by
        simp only [pow_two,←mul_assoc]
        simp only [mul_add]
        simp only [add_mul,mul_div,add_div]
        rw [le_,le₁,le₂,←add_assoc,add_rotate (a:=a*y*y),←mul_two]
        rw [mul_rotate (a:=b/2),mul_rotate (a:=y),le_',le_'',←pow_two]
        rw [le_''']
        assumption
        assumption

      have h₆: a*(y + b/2*a)^2 ≥ 0 := by
        sorry
      rw [←h₅] at h₄
      sorry  

    · sorry
    )

end QuadRoots

#check LinearOrder
#check LinearOrderedAddCommGroup
#check LinearOrderedCommRing
#check mul_lt_mul_of_pos_left
#check lt_of_le_of_ne
