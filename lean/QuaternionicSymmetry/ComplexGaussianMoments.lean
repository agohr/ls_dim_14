import QuaternionicSymmetry.GaussianRadialMoments

/-! The radial moments of the two-dimensional standard Gaussian.

These are polynomial identities and actual product-measure integrals.  No
complex Gaussian law is introduced here.
-/

namespace QuaternionicSymmetry.ComplexGaussianMoments

open scoped BigOperators
open GaussianPolynomialExpectation MvPolynomial MeasureTheory

noncomputable section

variable {S : Type*} [CommRing S] [Algebra ℝ S]

theorem expectation_radial_two (k : ℕ) :
    expectation ((GaussianRadialMoments.radial : MvPolynomial (Fin 2) S) ^ k) =
      (2 ^ k * k.factorial : ℕ) := by
  induction k with
  | zero => simp [GaussianRadialMoments.expectation_one]
  | succ k ih =>
      rw [GaussianRadialMoments.expectation_radial_succ, ih]
      rw [Nat.factorial_succ]
      simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add,
        Nat.cast_ofNat, Nat.cast_pow]
      ring

theorem integral_radial_two (k : ℕ) :
    (∫ x : Fin 2 → ℝ, ((∑ i, x i ^ 2) / 2) ^ k
      ∂GaussianPolynomialIntegration.standardMeasure) = (k.factorial : ℝ) := by
  have hrad :
      (∫ x : Fin 2 → ℝ, (∑ i, x i ^ 2) ^ k
        ∂GaussianPolynomialIntegration.standardMeasure) =
        (2 ^ k * k.factorial : ℝ) := by
    simpa only [map_pow, GaussianRadialMoments.eval_radial,
      expectation_radial_two (S := ℝ) k, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat] using
      GaussianPolynomialIntegration.integral_polynomial
        ((GaussianRadialMoments.radial : MvPolynomial (Fin 2) ℝ) ^ k)
  rw [show (fun x : Fin 2 → ℝ => ((∑ i, x i ^ 2) / 2) ^ k) =
      (fun x => (1 / (2 : ℝ)) ^ k * (∑ i, x i ^ 2) ^ k) by
        funext x
        ring]
  rw [integral_const_mul, hrad]
  calc
    (1 / (2 : ℝ)) ^ k * (2 ^ k * (k.factorial : ℝ)) =
        ((1 / (2 : ℝ)) ^ k * 2 ^ k) * (k.factorial : ℝ) := by ring
    _ = (k.factorial : ℝ) := by
      rw [← mul_pow]
      norm_num

end
end QuaternionicSymmetry.ComplexGaussianMoments
