/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Pietro Monticone
-/

import Mathlib.NumberTheory.Cyclotomic.Embeddings
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Third Cyclotomic Field
We gather various results about the third cyclotomic field.

## Main results
* `IsCyclotomicExtension.Rat.Three.Units.mem`: Given a unit `u : (𝓞 K)ˣ`, where `K` is a number
field such that `IsCyclotomicExtension {3} ℚ K`, then `u ∈ ({1, -1, ζ, -ζ, ζ^2, -ζ^2}`, where `ζ`
is any primitive `3`-rd root of unity in `K`.

* `IsCyclotomicExtension.Rat.Three.Units.mem.eq_one_or_neg_one_of_unit_of_congruent`: Given a unit
`u : (𝓞 K)ˣ`, where `K` is a number field such that `IsCyclotomicExtension {3} ℚ K`, if `u` is
congruent to an integer modulo `3`, then `u = 1` or `u = -1`. This is a special case of the
so-called *Kummer's lemma*.
-/

open NumberField Units InfinitePlace nonZeroDivisors Polynomial

namespace IsCyclotomicExtension.Rat.Three

/- Let `K` be a number field such that `IsCyclotomicExtension {3} ℚ K`. -/
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/- Let `ζ` be any primitive `3`-rd root of unity in `K` and `u` be a unit in `(𝓞 K)ˣ`. -/
variable {ζ : K} (hζ : IsPrimitiveRoot ζ ↑(3 : ℕ+)) (u : (𝓞 K)ˣ)

/- Let `η` be the element in the units of the ring of integers corresponding to `ζ`. -/
local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit

/- Let `λ` be the element in the ring of integers corresponding to `ζ - 1`. -/
local notation3 "λ" => hζ.toInteger - 1

lemma coe_eta : (η : 𝓞 K) = hζ.toInteger := rfl

noncomputable
instance : Fintype (𝓞 K ⧸ Ideal.span {λ}) := by
  refine Ideal.fintypeQuotientOfFreeOfNeBot _ (fun h ↦ ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero, ← Subtype.coe_inj] at h
  refine hζ.ne_one (by decide) ?_
  exact RingOfIntegers.ext_iff.1 h

/-- We have that `𝓞 K ⧸ Ideal.span {λ}` has cardinality `3`. -/
lemma card_quot : Fintype.card (𝓞 K ⧸ Ideal.span {λ}) = 3 := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  simp [hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)]

/-- We have that `2` in `𝓞 K ⧸ Ideal.span {λ}` is not `0`. -/
lemma two_ne_zero : (2 : 𝓞 K ⧸ Ideal.span {λ}) ≠ 0 := by
  suffices 2 ∉ Ideal.span {hζ.toInteger - 1} by
    intro h
    refine this (Ideal.Quotient.eq_zero_iff_mem.1 <| by simp [h])
  intro h
  rw [Ideal.mem_span_singleton] at h
  replace h : hζ.toInteger - 1 ∣ ↑(2 : ℤ) := by simp [h]
  rw [← Ideal.norm_dvd_iff, hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at h
  · norm_num at h
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)]
    exact Int.prime_three

/-- We have that `λ` does not divide `2`. -/
lemma lambda_not_dvd_two : ¬ λ ∣ 2 :=
  fun h ↦ two_ne_zero hζ <| Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.mem_span_singleton.2 h

instance : Nontrivial (𝓞 K ⧸ Ideal.span {λ}) := nontrivial_of_ne 2 0 <| two_ne_zero hζ

open Classical Finset in

/-- We have that the universal finite set is `{0, 1, -1}`. -/
lemma univ_quot : (univ : Finset ((𝓞 K ⧸ Ideal.span {λ}))) = {0, 1, -1} := by
  refine (eq_of_subset_of_card_le (fun _ _ ↦ mem_univ _) ?_).symm
  rw [card_univ, card_quot hζ, card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
  · rw [mem_singleton]
    intro h
    rw [← add_eq_zero_iff_eq_neg, one_add_one_eq_two] at h
    exact two_ne_zero hζ h
  · intro h
    simp only [mem_insert, mem_singleton, zero_eq_neg] at h
    rcases h with (h | h)
    · exact zero_ne_one h
    · exact zero_ne_one h.symm

/-- We have that `λ` divides `x` or `λ` divides `x - 1` or `λ` divides `x + 1`. -/
lemma dvd_or_dvd_sub_one_or_dvd_add_one (x : 𝓞 K) : λ ∣ x ∨ λ ∣ x - 1 ∨ λ ∣ x + 1 := by
  have := Finset.mem_univ (Ideal.Quotient.mk (Ideal.span {λ}) x)
  rw [univ_quot hζ] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with (h | h | h)
  · left
    exact Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 h
  · right; left
    refine Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_sub, h, RingHom.map_one, sub_self]
  · right; right
    refine Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_add, h, RingHom.map_one, add_left_neg]

/-- We have that `↑η = ζ`. -/
lemma _root_.IsPrimitiveRoot.toInteger_coe : hζ.toInteger.1 = ζ := rfl

/-- We have that `η ^ 3 = 1`. -/
lemma _root_.IsPrimitiveRoot.toInteger_cube_eq_one : η ^ 3 = 1 := by
  ext
  exact hζ.pow_eq_one

/-- We have that `η ^ 2 + η + 1 = 0`. -/
lemma _root_.IsPrimitiveRoot.toInteger_eval_cyclo : (η : 𝓞 K) ^ 2 + η + 1 = 0 := by
  ext; simpa using hζ.isRoot_cyclotomic (by decide)

/-- We have that `x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2)`. -/
lemma cube_sub_one (x : 𝓞 K) : x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2) := by
  symm
  calc _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + η ^ 3) - η ^ 3 := by ring
  _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + 1) - 1 := by
    norm_cast
    simp [hζ.toInteger_cube_eq_one]
  _ = x ^ 3 - 1 := by rw [hζ.toInteger_eval_cyclo]; ring

/-- We have that `λ` divides `x * (x - 1) * (x - (η + 1))`. -/
lemma lambda_dvd_mul_sub_one_mul_sub_eta_add_one (x : 𝓞 K) :
    λ ∣ x * (x - 1) * (x - (η + 1)) := by
  rcases dvd_or_dvd_sub_one_or_dvd_add_one hζ x with (h | h | h)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
  · refine dvd_mul_of_dvd_right ?_ _
    rw [show x - (η + 1) = x + 1 - (η - 1 + 3) by ring]
    exact dvd_sub h <| dvd_add dvd_rfl hζ.toInteger_sub_one_dvd_prime'

/-- If `λ` divides `x - 1`, then `λ ^ 4` divides `x ^ 3 - 1`. -/
lemma lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one {x : 𝓞 K} (h : λ ∣ x - 1) :
    λ ^ 4 ∣ x ^ 3 - 1 := by
  obtain ⟨y, hy⟩ := h
  have : x ^ 3 - 1 = λ ^ 3 * (y * (y - 1) * (y - (η + 1))) := by
    calc _ =  (x - 1) * (x - 1 - λ) * (x - 1 - λ * (η + 1)) := by
          simp only [coe_eta, cube_sub_one hζ x]; ring
    _ = _ := by rw [hy]; ring
  rw [this, show λ ^ 4 = λ ^ 3 * λ by ring]
  exact mul_dvd_mul dvd_rfl (lambda_dvd_mul_sub_one_mul_sub_eta_add_one hζ y)

/-- If `λ` divides `x + 1`, then `λ ^ 4` divides `x ^ 3 + 1`. -/
lemma lambda_pow_four_dvd_cube_add_one_of_dvd_add_one {x : 𝓞 K} (h : λ ∣ x + 1) :
    λ ^ 4 ∣ x ^ 3 + 1 := by
  replace h : λ ∣ -x - 1 := by
    obtain ⟨y, hy⟩ := h
    refine ⟨-y, ?_⟩
    rw [mul_neg, ← hy]
    ring
  obtain ⟨y, hy⟩ := lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one hζ h
  refine ⟨-y, ?_⟩
  rw [mul_neg, ← hy]
  ring

/-- If `λ` does not divide `x`, then `λ ^ 4` divides `x ^ 3 - 1` or `x ^ 3 + 1`. -/
lemma lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd {x : 𝓞 K} (h : ¬ λ ∣ x) :
    λ ^ 4 ∣ x ^ 3 - 1 ∨ λ ^ 4 ∣ x ^ 3 + 1 := by
  rcases dvd_or_dvd_sub_one_or_dvd_add_one hζ x with (H | H | H)
  · contradiction
  · left
    exact lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one hζ H
  · right
    exact lambda_pow_four_dvd_cube_add_one_of_dvd_add_one hζ H

end IsCyclotomicExtension.Rat.Three
