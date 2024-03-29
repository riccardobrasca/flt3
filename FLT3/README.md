# FLT3 (LFTCM 2024, Luminy)

## Team

- Riccardo Brasca (Université Paris-Cité)
- Sanyam Gupta (Sorbonne Université)
- Omar Haddad (Université Paris-Cité)
- David Lowry-Duda (ICERM)
- Lorenzo Luccioli (University of Bologna)
- Pietro Monticone (University of Trento)
- Alexis Saurin (CNRS Université Paris-Cité)
- Florent Schaffhauser (Heidelberg University)

## Motivation

- There was already a version of the formalised proof of FLT3 within FLT Regular Prime:
    - It was longer than ours
    - Less Mathlib style
- FLT Regular Prime: Alex, Chris, Eric, Ruben, Andrew, Riccardo and others.
- FLT by Kevin Buzzard and others

## Logistical Overview

- Textbook reference: Arithmetics by Marc Hindry https://link.springer.com/book/10.1007/978-1-4471-2131-2
- Previous work by Riccardo with 37 sorries left
- Seamless coordination between two teams communicating mostly through Zulip

## Mathematical Overview

- Some of us didn't know the mathematical prerequisites for the proof
- Sum of cubes equals a cube isn't informative
- Product of coprimes equals a cube is informative (implies that each factor is a cube)
- To express $a^3 + b^3$ as a product we need to work in $\mathbb{Z}[e^{\frac{2\pi i}{3}}]$ which is already in Mathlib

$$a^3+b^3 = (a+b)(a^2 - ab + b^2)
          = (a+b)(a + e^{\frac{2\pi i}{3}} b )(a+ e^{\frac{4\pi i}{3}} b)$$

- Sanyam et al.

## Lean Overview

### Created Lemmas

- lambda_ne_zero
- eta_add_one_inv
- x_mul_y_mul_z_eq_u_w_pow_three (omega,convert, multiplicity)

### Removed Lemmas
...
### Proved Lemmas

1. x_eq_unit_mul_cube (we by-passed Ideals)
2. formula2 (rw [show ... by ring], mul_left_cancel₀, multiplicity, congr, omega, )
3. by_kummer (<;> , rcases+replace)


- lambda_sq_not_a_add_eta_mul_b
- associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b (rw [show ... by ring])
- lambda_not_dvd_x (omega, multiplicity)

### PR to Mathlib

https://github.com/leanprover-community/mathlib4/pull/11695#event-12255417495

## Lean Showcase

1. x_eq_unit_mul_cube (we by-passed Ideals) https://github.com/riccardobrasca/flt3/blob/b2bb5436915e38cc01c43d9aa72496e2764fe249/FLT3/FLT3.lean#L794
2. formula2 (rw [show ... by ring], mul_left_cancel₀, multiplicity, congr, omega) https://github.com/riccardobrasca/flt3/blob/b2bb5436915e38cc01c43d9aa72496e2764fe249/FLT3/FLT3.lean#L989
3. by_kummer (<;> , rcases+replace) https://github.com/riccardobrasca/flt3/blob/b2bb5436915e38cc01c43d9aa72496e2764fe249/FLT3/FLT3.lean#L1051