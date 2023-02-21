import LowDegreeEquations.sqrt
import Mathlib

namespace Quadratic


noncomputable def root₁(a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0): ℝ := (-b + ℝ.sqrt (b^2 - 4*a*c) h) / (2*a)
noncomputable def root₂(a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0): ℝ := (-b - ℝ.sqrt (b^2 - 4*a*c) h) / (2*a) 

theorem root₁_is_root (a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0) (h': a≠0): a*(root₁ a b c h)^2 + b*(root₁ a b c h) + c = 0 := by
  sorry

theorem root₂_is_root (a b c : ℝ) (h:(b^2 - 4*a*c) ≥ 0) (h': a≠0): a*(root₂ a b c h)^2 + b*(root₂ a b c h) + c = 0 := by
  sorry


end Quadratic
