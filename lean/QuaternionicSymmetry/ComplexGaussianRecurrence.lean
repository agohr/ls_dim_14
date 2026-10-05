import QuaternionicSymmetry.ComplexGaussianLinearMoments

/-!
  Integration-by-parts recurrences for weighted linear statistics under the
  factorial complex-radial Gaussian polynomial functional.
-/

namespace QuaternionicSymmetry.ComplexGaussianRecurrence

open scoped BigOperators
open MvPolynomial ComplexGaussianPolynomial ComplexGaussianRadialMoments
open QuaternionicSymmetry.ComplexGaussianLinearMoments

noncomputable section

variable {β S : Type*} [Fintype β] [DecidableEq β] [CommRing S] [Algebra ℝ S]

/-- The coefficientwise product of two weight families. -/
def pointwiseProduct (φ θ : β → S) : β → S := fun i => φ i * θ i

omit [Algebra ℝ S] in
private theorem pderiv_linearPolynomial (θ : β → S) (i : β) :
    pderiv i (linearPolynomial θ) = MvPolynomial.C (θ i) := by
  simp [linearPolynomial, map_sum, Pi.single_apply, Finset.sum_ite_eq']

omit [Algebra ℝ S] in
private theorem pderiv_linear_pow (θ : β → S) (i : β) (k : ℕ) :
    pderiv i (linearPolynomial θ ^ (k + 1)) =
      (k + 1) • (linearPolynomial θ ^ k * MvPolynomial.C (θ i)) := by
  rw [pderiv_pow, pderiv_linearPolynomial]
  simp only [nsmul_eq_mul]
  rw [show k + 1 - 1 = k by omega]
  ring

/-- One integration-by-parts step for two weighted linear statistics. -/
theorem expectation_linear_mul_pow_succ (φ θ : β → S) (k : ℕ) :
    expectation (linearPolynomial φ * linearPolynomial θ ^ (k + 1)) =
      (∑ i, φ i) * expectation (linearPolynomial θ ^ (k + 1)) +
        (k + 1) • expectation
          (linearPolynomial (pointwiseProduct φ θ) * linearPolynomial θ ^ k) := by
  calc
    expectation (linearPolynomial φ * linearPolynomial θ ^ (k + 1)) =
        ∑ i, φ i * expectation (MvPolynomial.X i * linearPolynomial θ ^ (k + 1)) := by
      rw [linearPolynomial, Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, MvPolynomial.C_mul', map_smul, smul_eq_mul]
    _ = ∑ i, φ i *
        (expectation (linearPolynomial θ ^ (k + 1)) +
          expectation (MvPolynomial.X i * pderiv i (linearPolynomial θ ^ (k + 1)))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [expectation_mul]
    _ = (∑ i, φ i) * expectation (linearPolynomial θ ^ (k + 1)) +
        (k + 1) • expectation
          (linearPolynomial (pointwiseProduct φ θ) * linearPolynomial θ ^ k) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [show (fun i => φ i * expectation
          (MvPolynomial.X i * pderiv i (linearPolynomial θ ^ (k + 1)))) =
          (fun i => φ i * (k + 1) • expectation
            (MvPolynomial.X i * (linearPolynomial θ ^ k * MvPolynomial.C (θ i)))) by
            funext i
            rw [pderiv_linear_pow]
            have hmul : MvPolynomial.X i *
                ((k + 1) • (linearPolynomial θ ^ k * MvPolynomial.C (θ i))) =
                (k + 1) • (MvPolynomial.X i *
                  (linearPolynomial θ ^ k * MvPolynomial.C (θ i))) := by
              simp only [nsmul_eq_mul]
              ring
            rw [hmul, map_nsmul]]
      simp only [nsmul_eq_mul]
      have hcoeff : (∑ i, (φ i * θ i) *
          expectation (MvPolynomial.X i * linearPolynomial θ ^ k)) =
          expectation (linearPolynomial (pointwiseProduct φ θ) * linearPolynomial θ ^ k) := by
        change (∑ i, (φ i * θ i) *
            expectation (MvPolynomial.X i * linearPolynomial θ ^ k)) =
          expectation ((∑ i, MvPolynomial.C (φ i * θ i) * MvPolynomial.X i) *
            linearPolynomial θ ^ k)
        rw [Finset.sum_mul, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_assoc, MvPolynomial.C_mul', smul_mul_assoc, map_smul, smul_eq_mul]
        ring
      rw [show (∑ i, φ i *
          ((↑(k + 1) : S) * expectation
            (MvPolynomial.X i * (linearPolynomial θ ^ k * MvPolynomial.C (θ i))))) =
          (k + 1) • ∑ i, (φ i * θ i) *
            expectation (MvPolynomial.X i * linearPolynomial θ ^ k) by
            simp only [nsmul_eq_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [show MvPolynomial.X i * (linearPolynomial θ ^ k * MvPolynomial.C (θ i)) =
                MvPolynomial.C (θ i) * (MvPolynomial.X i * linearPolynomial θ ^ k) by ring]
            rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]
            ring, hcoeff]
      simp only [nsmul_eq_mul]

end
end QuaternionicSymmetry.ComplexGaussianRecurrence
