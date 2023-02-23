import LowDegreeEquations.sqrt
import Mathlib

namespace Quadratic


noncomputable def root₁ (a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0): ℝ := (-b + ℝ.sqrt (b^2 - 4*a*c) h) / (2*a)
noncomputable def root₂(a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0): ℝ := (-b - ℝ.sqrt (b^2 - 4*a*c) h) / (2*a) 

--private axiom two_mul_two: (2:ℝ)*2 = 4
def two_mul_two (R : Type) [Ring R] : (4: R) = (2 : R) * (2: R) := by /-divide and multiply by 2*2(:ℝ) = 4(:ℝ) -/
    have : (2: R) = (1: R) + (1: R) := by norm_cast
    rw [this, mul_add, mul_one]
    norm_cast

private lemma l₁ (a b c : ℝ) (h:(b*b - 4*a*c) ≥ 0) (h': a≠0): (b * ((-b + ℝ.sqrt (b * b - 4*a*c) h) / (2 * a))) = ((-(2*a*b*b)/(4*a*a)) + ((2*a*b*(ℝ.sqrt (b * b - 4*a*c) h))/(4*a*a))) := by
  have h' : 2*a ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, h', or_self, not_false_iff] 
  conv=>
    lhs
    simp only [add_div,mul_div,mul_add, add_mul]
    rw [←mul_div_mul_right (c:=2*a) (hc:=h')] /-divide and multiply by 2*a -/
    rw [←mul_div_mul_right (c:=2*a) (a:=b * ℝ.sqrt (b * b - 4 * a * c) h) (b := 2*a) (hc:=h')] /-divide and multiply by 2*a -/
    simp [mul_left_comm (a:=b) (b:=2) (c:=a)]
    rw [mul_left_comm,mul_right_comm,mul_assoc]
    rw [←mul_left_comm (a:=a) (b:=b) (c:=b)]
    rw [mul_mul_mul_comm]
    rw [mul_rotate (a:=b) (b:=(ℝ.sqrt (b * b - 4 * a * c) h)) (c:=2*a)]
    rw [mul_rotate (a:=ℝ.sqrt (b * b - 4 * a * c) h) (b:=2*a) (c:=b)]
    simp only [←mul_assoc]
    simp [←two_mul_two]

private lemma l₂ (a b c : ℝ) (h:(b*b - 4*a*c) ≥ 0):
  a *((-b * -b + ℝ.sqrt (b * b - 4 * a * c) h * -b +
        (-b * ℝ.sqrt (b * b - 4 * a * c) h +
          ℝ.sqrt (b * b - 4 * a * c) h * ℝ.sqrt (b * b - 4 * a * c) h)) /
              (2 * (2 * a * a))) = 
                (2*a*b*b - 4*a*a*c - 2*a*b*ℝ.sqrt (b*b - 4*a*c) h)/(4*a*a) := by
                conv=>
                  lhs
                  rw [ℝ.sqrt_mul_self (b*b - 4*a*c) h]
                  simp only [mul_div,mul_add,mul_sub]
                  simp only [←mul_assoc]
                  simp [←two_mul_two]
                  rw [mul_right_comm (a:=a) (b:=ℝ.sqrt (b*b - 4*a*c) h) (c:=b)]
                  rw [←add_assoc]
                ring


theorem root₁_is_root (a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0) (h': a≠0): a*(root₁ a b c h)^2 + b*(root₁ a b c h) + c = 0 := by
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

private lemma l'₁ (a b c : ℝ) (h:(b*b - 4*a*c) ≥ 0) (h': a≠0): (b * ((-b - ℝ.sqrt (b * b - 4*a*c) h) / (2 * a))) = ((-(2*a*b*b)/(4*a*a)) - ((2*a*b*(ℝ.sqrt (b * b - 4*a*c) h))/(4*a*a))) := by
  have h' : 2*a ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, h', or_self, not_false_iff] 
  conv=>
    lhs
    simp only [sub_div,mul_div,mul_sub, add_mul]
    rw [←mul_div_mul_right (c:=2*a) (hc:=h')] /-divide and multiply by 2*a -/
    rw [←mul_div_mul_right (c:=2*a) (a:=b * ℝ.sqrt (b * b - 4 * a * c) h) (b := 2*a) (hc:=h')] /-divide and multiply by 2*a -/  
    simp [mul_left_comm (a:=b) (b:=2) (c:=a)]
    rw [mul_left_comm,mul_right_comm,mul_assoc]
    rw [←mul_left_comm (a:=a) (b:=b) (c:=b)]
    rw [mul_mul_mul_comm]
    rw [mul_rotate (a:=b) (b:=(ℝ.sqrt (b * b - 4 * a * c) h)) (c:=2*a)]
    rw [mul_rotate (a:=ℝ.sqrt (b * b - 4 * a * c) h) (b:=2*a) (c:=b)]
    simp only [←mul_assoc]
    simp [←two_mul_two]

-- set_option pp.all true in 
--set_option maxHeartbeats 500000 in
private lemma l'₂ (a b c : ℝ) (h:(b*b - 4*a*c) ≥ 0) (h': a≠0): 
  a *((-b * -b + -ℝ.sqrt (b * b - 4 * a * c) h * -b +
          (-b * -ℝ.sqrt (b * b - 4 * a * c) h +
            -ℝ.sqrt (b * b - 4 * a * c) h * -ℝ.sqrt (b * b - 4 * a * c) h)) /
                (2 * (2 * a * a))) = 
                  (2*a*b*b - 4*a*a*c - 2*a*b*ℝ.sqrt (b*b - 4*a*c) h)/(4*a*a) := by
                    have l: -ℝ.sqrt (b * b - 4 * a * c) h * -ℝ.sqrt (b * b - 4 * a * c) h =
                      ℝ.sqrt (b * b - 4 * a * c) h * ℝ.sqrt (b * b - 4 * a * c) h := by
                      rw [neg_mul_neg]
                    rw[l]
                    have l₁: -b*-b = b*b := by
                      rw [neg_mul_neg]
                    rw[l₁]
                    have l₂: -b*-ℝ.sqrt (b * b - 4 * a * c) h = b*ℝ.sqrt (b * b - 4 * a * c) h := by
                      rw [neg_mul_neg]  
                    rw[l₂]
                    have l₃: -ℝ.sqrt (b * b - 4 * a * c) h * -b = b*ℝ.sqrt (b * b - 4 * a * c) h:= by
                      rw [neg_mul_neg,mul_comm]
                    rw[l₃]
                    conv=>  
                      lhs
                      rw [ℝ.sqrt_mul_self (b*b - 4*a*c) h]
                      simp only [mul_div,mul_add,mul_sub]
                      simp only [←mul_assoc]
                      simp [←two_mul_two]
                      --rw [mul_right_comm (a:=a) (b:=ℝ.sqrt (b*b - 4*a*c) h) (c:=b)]
                      rw [←add_assoc]
                      rw [add_sub]
                      rw [←mul_two (a:=a*b*b)]
                      sorry
                      --rw [←mul_two (a:=a * b * ℝ.sqrt (b * b - 4 * a * c) h)]
                    ring
                    

theorem root₂_is_root (a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0) (h': a≠0): a*(root₂ a b c h)^2 + b*(root₂ a b c h) + c = 0 := by
  simp only [root₂, div_pow]
  simp only [pow_two, mul_left_comm, mul_sub, sub_mul] at h ⊢
  rw [l'₁ (h':=h')]
  sorry

end Quadratic
