import QuaternionicSymmetry.GaussianRadialMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Polynomial.Coeff

/-! Gaussian expectations of products of radial quadratic factors. -/

namespace QuaternionicSymmetry.GaussianRadialProduct

open scoped BigOperators
open MvPolynomial GaussianPolynomialExpectation GaussianRadialMoments

noncomputable section

variable {β S : Type*} [DecidableEq β] [CommRing S] [Algebra ℝ S]

private theorem expectation_C_mul (c : S) (p : MvPolynomial (Fin 3) S) :
    expectation (C c * p) = c * expectation p := by
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem expectation_product (s : Finset β) (z : S) (w : β → S) :
    expectation (∏ j ∈ s, ((radial : MvPolynomial (Fin 3) S) - C (z * w j))) =
      ∑ t ∈ s.powerset, (-1 : S) ^ t.card * z ^ t.card * (∏ j ∈ t, w j) *
        (Nat.doubleFactorial (2 * (s.card - t.card) + 1) : S) := by
  rw [Finset.prod_sub, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hts : t ⊆ s := Finset.mem_powerset.mp ht
  have hcard : (s \ t).card = s.card - t.card := Finset.card_sdiff_of_subset hts
  rw [Finset.prod_const, hcard]
  have hterm :
      (-1 : MvPolynomial (Fin 3) S) ^ t.card * radial ^ (s.card - t.card) *
        (∏ j ∈ t, C (z * w j)) =
      C ((-1 : S) ^ t.card * z ^ t.card * ∏ j ∈ t, w j) * radial ^ (s.card - t.card) := by
    simp only [← map_prod, Finset.prod_mul_distrib, Finset.prod_const,
      map_mul, map_pow, map_neg, map_one]
    ring
  rw [hterm, expectation_C_mul, expectation_radial_three]

/-- The elementary symmetric sum is kept as a finite subset sum. -/
def elementary (s : Finset β) (w : β → S) (k : ℕ) : S :=
  ∑ t ∈ s.powersetCard k, ∏ j ∈ t, w j

theorem expectation_product_grouped (s : Finset β) (z : S) (w : β → S) :
    expectation (∏ j ∈ s, ((radial : MvPolynomial (Fin 3) S) - C (z * w j))) =
      ∑ k ∈ Finset.range (s.card + 1), (-1 : S) ^ k * z ^ k * elementary s w k *
        (Nat.doubleFactorial (2 * (s.card - k) + 1) : S) := by
  rw [expectation_product, Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro k _
  simp only [elementary, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(Finset.mem_powersetCard.mp ht).2]

omit [DecidableEq β] in
theorem elementary_sq_nonneg (s : Finset β) (lam : β → ℝ) (k : ℕ) :
    0 ≤ elementary s (fun j => lam j ^ 2) k := by
  apply Finset.sum_nonneg
  intro t _
  exact Finset.prod_nonneg (fun j _ => sq_nonneg (lam j))

/-- Keep the radial shift as a formal variable for coefficient extraction. -/
theorem expectation_product_polynomial (s : Finset β) (w : β → ℝ) :
    expectation (∏ j ∈ s, ((radial : MvPolynomial (Fin 3) (Polynomial ℝ)) -
      C (Polynomial.X * Polynomial.C (w j)))) =
      ∑ k ∈ Finset.range (s.card + 1),
        Polynomial.C ((-1 : ℝ) ^ k * elementary s w k *
          (Nat.doubleFactorial (2 * (s.card - k) + 1) : ℝ)) * Polynomial.X ^ k := by
  rw [expectation_product_grouped]
  apply Finset.sum_congr rfl
  intro k _
  have hel : elementary s (fun j => Polynomial.C (w j)) k =
      Polynomial.C (elementary s w k) := by
    simp [elementary]
  rw [hel]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

theorem coeff_expectation_product (s : Finset β) (w : β → ℝ) (k : ℕ) (hk : k ≤ s.card) :
    (expectation (∏ j ∈ s, ((radial : MvPolynomial (Fin 3) (Polynomial ℝ)) -
      C (Polynomial.X * Polynomial.C (w j))))).coeff k =
        (-1 : ℝ) ^ k * elementary s w k *
          (Nat.doubleFactorial (2 * (s.card - k) + 1) : ℝ) := by
  rw [expectation_product_polynomial, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

theorem signed_coeff_expectation_product_nonneg (s : Finset β) (lam : β → ℝ)
    (k : ℕ) (hk : k ≤ s.card) :
    0 ≤ (-1 : ℝ) ^ k *
      (expectation (∏ j ∈ s, ((radial : MvPolynomial (Fin 3) (Polynomial ℝ)) -
        C (Polynomial.X * Polynomial.C (lam j ^ 2))))).coeff k := by
  rw [coeff_expectation_product s _ k hk, ← mul_assoc, ← mul_assoc, ← pow_add,
    show k + k = 2 * k by omega, pow_mul, neg_one_sq, one_pow, one_mul]
  exact mul_nonneg (elementary_sq_nonneg s lam k) (Nat.cast_nonneg _)

omit [DecidableEq β] in
theorem elementary_algebraMap (s : Finset β) (w : β → ℝ) (k : ℕ) :
    elementary s (fun j => algebraMap ℝ S (w j)) k =
      algebraMap ℝ S (elementary s w k) := by
  simp [elementary]

theorem expectation_product_polynomial_sq (s : Finset β) (w : β → S) :
    expectation (∏ j ∈ s, ((radial : MvPolynomial (Fin 3) (Polynomial S)) -
      C (Polynomial.X ^ 2 * Polynomial.C (w j)))) =
      ∑ k ∈ Finset.range (s.card + 1),
        Polynomial.C ((-1 : S) ^ k * elementary s w k *
          (Nat.doubleFactorial (2 * (s.card - k) + 1) : S)) * Polynomial.X ^ (2 * k) := by
  rw [expectation_product_grouped]
  apply Finset.sum_congr rfl
  intro k _
  have hel : elementary s (fun j => Polynomial.C (w j)) k =
      Polynomial.C (elementary s w k) := by
    simp [elementary]
  rw [hel]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, ← pow_mul]
  ring

theorem coeff_expectation_product_sq (s : Finset β) (w : β → S)
    (k : ℕ) (hk : k ≤ s.card) :
    (expectation (∏ j ∈ s, ((radial : MvPolynomial (Fin 3) (Polynomial S)) -
      C (Polynomial.X ^ 2 * Polynomial.C (w j))))).coeff (2 * k) =
        (-1 : S) ^ k * elementary s w k *
          (Nat.doubleFactorial (2 * (s.card - k) + 1) : S) := by
  rw [expectation_product_polynomial_sq, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [show 2 * k ≠ 2 * j by omega]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

end
end QuaternionicSymmetry.GaussianRadialProduct
