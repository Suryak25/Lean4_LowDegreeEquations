import LowDegreeEquations.sqrt
import Mathlib

namespace Quadratic


noncomputable def root₁ (a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0): ℝ := (-b + ℝ.sqrt (b^2 - 4*a*c) h) / (2*a)
noncomputable def root₂(a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0): ℝ := (-b - ℝ.sqrt (b^2 - 4*a*c) h) / (2*a) 

private axiom two_mul_two: (2:ℝ)*2 = 4


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
    --show (-(2 * a * b * b))/ (4 * a * a) + 2 * a * b * ℝ.sqrt (b * b - 4 * a * c) h / (4* a * a)
  rw [two_mul_two]


theorem root₁_is_root (a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0) (h': a≠0): a*(root₁ a b c h)^2 + b*(root₁ a b c h) + c = 0 := by
  simp only [root₁, div_pow]
  simp only [pow_two, mul_left_comm, mul_add, add_mul] at h ⊢
  rw [l₁ (h':=h')]
  --show a * (((-b + ℝ.sqrt (b ^ 2 - 4 * a * c) h)*(-b + ℝ.sqrt (b ^ 2 - 4 * a * c) h))/ ((2 * a)*(2 * a)) ) + b * ((-b + ℝ.sqrt (b ^ 2 - 4 * a * c) h) / (2 * a)) + c =0
  sorry
  



theorem root₂_is_root (a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0) (h': a≠0): a*(root₂ a b c h)^2 + b*(root₂ a b c h) + c = 0 := by
  sorry


end Quadratic
