# Lean4 LowDegreeEquations
[![ci](https://github.com/Suryak25/Lean4_LowDegreeEquations/actions/workflows/build.yaml/badge.svg?event=push)](https://github.com/Suryak25/Lean4_LowDegreeEquations/actions/workflows/build.yaml)

Formalising and Implementation of Proof to the solutions of low degree equations (Quadratic equation and possibly cubic) in Lean4
## Introduction
In algebra the Quadratic equation in one variable is of the form $ax^2+bx+c = 0$, where $a$ is non-zero. The solutions of this equation are called **roots** of the Quadratic function defined by the left hand side of the equation. The roots of the quadratic function be found using the quadratic formula. The Quadratic formula is an algebric expression using the three coefficients of the quadratic equation, basic mathematical operations and $n^{th}$ root (radicals). Quadratic formula: $x=\frac{-b\pm\sqrt{b^2-4ac}}{2a}$.

This project is an attempt to formalise, implement and prove solutions to quadratic and possibly cubic equations (Low degree equations) in lean4.

## Road Map
* Implementing quadratic equation and its roots (only real solutions as $\mathbb{C}$ is not yet ported to lean4).
* Proving the roots are actually the solution to the quadratic equation.
* Proving that for a Quadratic equation there exist atmost two roots (distinct roots).
* Proving that if roots exist for a Quadratic equation and then how many roots (Two distinct or one unique)
* No solution case, proving no y exist for all Quadratic eqns with Discriminant < 0. The proof has two cases: a > 0 and a < 0.
## Completed
* Implementing quadratic equation and its roots (for all a b c x : $\mathbb{R}$)
* Proving the roots are actually the solution to the quadratic equation.
* Proving that for a Quadratic equation there exist atmost two roots (distinct roots).
* Proving that if roots exist for a Quadratic equation and then how many roots (Two distinct or one unique)
* No solution for both a > 0 and a < 0 cases proved.
## References
* [Proofwiki](https://proofwiki.org/wiki/Definition:Quadratic_Equation#:~:text=An%20algebraic%20equation%20of%20the,b2%E2%88%92aca)
* [Wikipedia](https://en.wikipedia.org/wiki/Quadratic_equation)
* [OtherProofs](https://math.stackexchange.com/questions/1688685/how-can-we-prove-that-a-quadratic-equation-has-at-most-2-roots#:~:text=If%20a%20non%20constant%20polynomial,be%20at%20most%20two%20factors.&text=This%20is%20a%20proof%20that,(x%E2%88%92b%E2%80%B2))
