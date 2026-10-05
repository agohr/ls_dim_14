import QuaternionicSymmetry.ComplexGaussianRadialMoments

/-!
  Low-order moments of a linear statistic for the factorial complex-radial
  Gaussian polynomial functional.
-/

namespace QuaternionicSymmetry.ComplexGaussianLinearMoments

open scoped BigOperators
open MvPolynomial ComplexGaussianPolynomial ComplexGaussianRadialMoments

noncomputable section

variable {β S : Type*} [Fintype β] [DecidableEq β] [CommRing S] [Algebra ℝ S]

/-- A weighted linear statistic in the independent complex-radial variables. -/
def linearPolynomial (θ : β → S) : MvPolynomial β S :=
  ∑ i, MvPolynomial.C (θ i) * MvPolynomial.X i

private theorem expectation_C_mul_X (a : S) (i : β) :
    expectation (MvPolynomial.C a * MvPolynomial.X i : MvPolynomial β S) = a := by
  rw [MvPolynomial.C_mul_X_eq_monomial]
  rw [expectation_monomial]
  simp only [monomialMoment]
  rw [Finset.prod_eq_one]
  · simp
  · intro j _
    by_cases h : j = i <;> simp [h]

omit [Algebra ℝ S] in
private theorem pderiv_linearPolynomial (θ : β → S) (i : β) :
    pderiv i (linearPolynomial θ) = MvPolynomial.C (θ i) := by
  simp [linearPolynomial, map_sum, Pi.single_apply, Finset.sum_ite_eq']

theorem expectation_linear (θ : β → S) :
    expectation (linearPolynomial θ) = ∑ i, θ i := by
  rw [linearPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact expectation_C_mul_X (θ i) i

private theorem expectation_X_mul_linear (θ : β → S) (i : β) :
    expectation (MvPolynomial.X i * linearPolynomial θ) = (∑ j, θ j) + θ i := by
  rw [expectation_mul, expectation_linear, pderiv_linearPolynomial]
  rw [mul_comm, expectation_C_mul_X]

theorem expectation_linear_sq (θ : β → S) :
    expectation (linearPolynomial θ ^ 2) =
      (∑ i, θ i) ^ 2 + ∑ i, θ i ^ 2 := by
  calc
    expectation (linearPolynomial θ ^ 2) =
        expectation ((∑ i, MvPolynomial.C (θ i) * MvPolynomial.X i) *
          linearPolynomial θ) := by
      rw [pow_two]
      rfl
    _ = ∑ i, θ i * expectation (MvPolynomial.X i * linearPolynomial θ) := by
      rw [Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, MvPolynomial.C_mul', map_smul, smul_eq_mul]
    _ = (∑ i, θ i) ^ 2 + ∑ i, θ i ^ 2 := by
      rw [show (fun i => θ i * expectation (MvPolynomial.X i * linearPolynomial θ)) =
          (fun i => θ i * ((∑ j, θ j) + θ i)) by
            funext i
            rw [expectation_X_mul_linear]]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [pow_two]

omit [Algebra ℝ S] in
private theorem pderiv_linear_sq (θ : β → S) (i : β) :
    pderiv i (linearPolynomial θ ^ 2) =
      MvPolynomial.C (θ i) * linearPolynomial θ +
        linearPolynomial θ * MvPolynomial.C (θ i) := by
  rw [pow_two, pderiv_mul, pderiv_linearPolynomial]

omit [DecidableEq β] in
private theorem expectation_X_mul_C_mul_linear (θ : β → S) (i : β) :
    expectation (MvPolynomial.X i * (MvPolynomial.C (θ i) * linearPolynomial θ)) =
      θ i * expectation (MvPolynomial.X i * linearPolynomial θ) := by
  rw [show MvPolynomial.X i * (MvPolynomial.C (θ i) * linearPolynomial θ) =
      MvPolynomial.C (θ i) * (MvPolynomial.X i * linearPolynomial θ) by ring]
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]

private theorem expectation_X_mul_linear_sq (θ : β → S) (i : β) :
    expectation (MvPolynomial.X i * linearPolynomial θ ^ 2) =
      (∑ j, θ j) ^ 2 + ∑ j, θ j ^ 2 +
        2 * θ i * ((∑ j, θ j) + θ i) := by
  rw [expectation_mul, expectation_linear_sq, pderiv_linear_sq, mul_add, map_add,
    expectation_X_mul_C_mul_linear]
  rw [show MvPolynomial.X i * (linearPolynomial θ * MvPolynomial.C (θ i)) =
      MvPolynomial.X i * (MvPolynomial.C (θ i) * linearPolynomial θ) by ring,
    expectation_X_mul_C_mul_linear]
  rw [expectation_X_mul_linear]
  ring

theorem expectation_linear_cube (θ : β → S) :
    expectation (linearPolynomial θ ^ 3) =
      (∑ i, θ i) ^ 3 + 3 * (∑ i, θ i) * (∑ i, θ i ^ 2) +
        2 * ∑ i, θ i ^ 3 := by
  calc
    expectation (linearPolynomial θ ^ 3) =
        expectation ((∑ i, MvPolynomial.C (θ i) * MvPolynomial.X i) *
          linearPolynomial θ ^ 2) := by
      rw [pow_succ']
      rfl
    _ = ∑ i, θ i * expectation (MvPolynomial.X i * linearPolynomial θ ^ 2) := by
      rw [Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, MvPolynomial.C_mul', map_smul, smul_eq_mul]
    _ = (∑ i, θ i) ^ 3 + 3 * (∑ i, θ i) * (∑ i, θ i ^ 2) +
        2 * ∑ i, θ i ^ 3 := by
      simp_rw [expectation_X_mul_linear_sq]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hq : (∑ i, θ i * (2 * θ i * ∑ j, θ j)) =
          2 * (∑ j, θ j) * ∑ i, θ i ^ 2 := by
        calc
          _ = ∑ i, (2 * ∑ j, θ j) * θ i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by rw [← Finset.mul_sum]
      have hr : (∑ i, θ i * (2 * θ i * θ i)) = 2 * ∑ i, θ i ^ 3 := by
        calc
          _ = ∑ i, 2 * θ i ^ 3 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by rw [Finset.mul_sum]
      have hs3 : (∑ i, θ i * (∑ j, θ j) ^ 2) = (∑ j, θ j) ^ 3 := by
        rw [← Finset.sum_mul]
        ring
      have hsq : (∑ i, θ i * ∑ j, θ j ^ 2) =
          (∑ i, θ i) * ∑ j, θ j ^ 2 := by
        rw [← Finset.sum_mul]
      rw [hq, hr, hs3, hsq]
      ring

end
end QuaternionicSymmetry.ComplexGaussianLinearMoments
