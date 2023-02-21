# Lean4 Cubic Formula
[![ci](https://github.com/Suryak25/Lean4_Cubic_Formula/actions/workflows/build.yaml/badge.svg?event=push)](https://github.com/Suryak25/Lean4_Cubic_Formula/actions/workflows/build.yaml)

Implentation and Proof of solutions of low degree equations (Quadratic and Cubic equations) in Lean4
## Introduction
In algebra the cubic equation in one variable is of the form $ax^3+bx^2+cx+d = 0$, where $a$ is non-zero. The solutions of this equation are called **roots** of the cubic function defined by the left hand side of the equation. The roots of the cubic equation can be found using Cardano's Formula. The Cardano's formula is an algebric expression using the four coefficients of the cubic equation, basic mathematical operations and $n^{th}$ root (radicals).  
This project is an attempt to implement and prove solutions to quadratic and cubic equations (Low degree equations) in lean4.

## Road Map
* Implementing and proving solutions of quadratic equations (only real solutions as $\mathbb{C}$ is not yet ported to lean4)
* Implementing and proving Cardano's formula.
* Proving that Cardano's roots are actually the roots of the cubic equation.
* Proving that Cardano's roots are the only roots of the cubic equation.

## References
* [Proofwiki](https://proofwiki.org/wiki/Cardano%27s_Formula)
* [Wikipedia](https://en.wikipedia.org/wiki/Cubic_equation)
