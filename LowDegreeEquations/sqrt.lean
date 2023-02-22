import Mathlib

opaque ℝ.sqrt (x: ℝ) : x ≥ 0 → ℝ

axiom ℝ.sqrt_pos (x: ℝ) : (pf : x ≥ 0) → ℝ.sqrt x pf ≥ 0

axiom ℝ.sqrt_mul_self (x: ℝ) : (pf : x ≥ 0) → (ℝ.sqrt x pf) * (ℝ.sqrt x pf) = x
