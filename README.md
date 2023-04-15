# Lean4 LowDegreeEquations
[![ci](https://github.com/Suryak25/Lean4_Cubic_Formula/actions/workflows/build.yaml/badge.svg?event=push)](https://github.com/Suryak25/Lean4_Cubic_Formula/actions/workflows/build.yaml)

Implentation and Proof of solutions of low degree equations (Quadratic equation and possibly cubic) in Lean4
## Introduction
In algebra the Quadratic equation in one variable is of the form $ax^2+bx+c = 0$, where $a$ is non-zero. The solutions of this equation are called **roots** of the Quadratic function defined by the left hand side of the equation. The roots of the quadratic function be found using the quadratic formula. The Quadratic formula is an algebric expression using the three coefficients of the quadratic equation, basic mathematical operations and $n^{th}$ root (radicals). Quadratic formula: $x = (-b \pm \sqrt{b^2 - 4*a*c})/(2*a)$  
This project is an attempt to implement and prove solutions to quadratic and cubic equations (Low degree equations) in lean4.

## Road Map
* Implementing quadratic equations and its roots (only real solutions as $\mathbb{C}$ is not yet ported to lean4)
* Proving the roots are actually the solution to the quadratic equation.
* Proving that if roots exist for a Quadratic equation and then how many roots (Two distinct or one unique)
* Proving that for a Quadratic equation there exist atmost two roots (distinct roots).
## Completed
* Implementing quadratic equations and its roots
* Proving the roots are actually the solution to the quadratic equation.
## References
* [Proofwiki](https://proofwiki.org/wiki/Definition:Quadratic_Equation#:~:text=An%20algebraic%20equation%20of%20the,b2%E2%88%92aca)
* [Wikipedia](https://en.wikipedia.org/wiki/Quadratic_equation)
* [OtherProofs](https://math.stackexchange.com/questions/1688685/how-can-we-prove-that-a-quadratic-equation-has-at-most-2-roots#:~:text=If%20a%20non%20constant%20polynomial,be%20at%20most%20two%20factors.&text=This%20is%20a%20proof%20that,(x%E2%88%92b%E2%80%B2))
