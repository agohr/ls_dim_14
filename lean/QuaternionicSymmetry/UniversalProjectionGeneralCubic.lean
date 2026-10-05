import QuaternionicSymmetry.UnitaryProjectionGeneralCubic
import QuaternionicSymmetry.UniversalProjectionMatrixMoments

/-! Cubic projection moments of every rank as universal matrix identities. -/
namespace QuaternionicSymmetry.UniversalProjectionGeneralCubic

open Matrix MeasureTheory UnitaryProjectionGeneralCubic HermitianProjectionMoments
  UnitaryProjectionDiagonal MvPolynomial

noncomputable section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The exchangeable cubic trace polynomial with real coefficients. -/
def cubicValue {S : Type*} [CommRing S] [Algebra ℝ S]
    (r ell : ℝ) (z1 z2 z3 : S) : S :=
  algebraMap ℝ S (distinctCoefficient r ell) * z1 ^ 3 +
  algebraMap ℝ S (3 * (pairCoefficient r ell - distinctCoefficient r ell)) * z1 * z2 +
  algebraMap ℝ S (sameCoefficient r ell - 3 * pairCoefficient r ell +
    2 * distinctCoefficient r ell) * z3

theorem integral_trace_cube (s : Finset κ) (hr : 3 ≤ Fintype.card κ)
    (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    (∫ U : Matrix.unitaryGroup κ ℂ,
      (Matrix.trace (UnitaryProjection.projection s U * Y)).re ^ 3
        ∂UnitaryHaarMeasure.probability) =
      cubicValue (Fintype.card κ) s.card (Matrix.trace Y).re
        (Matrix.trace (Y ^ 2)).re (Matrix.trace (Y ^ 3)).re := by
  have he (U : Matrix.unitaryGroup κ ℂ) :
      (Matrix.trace (UnitaryProjection.projection s U * Y)).re =
        ∑ i, hY.eigenvalues i * entry s (hY.eigenvectorUnitary⁻¹ * U) i := by
    conv_lhs => rw [hY.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [trace_conjugate]
    exact trace_diagonal s _ hY.eigenvalues
  simp_rw [he]
  rw [UnitaryHaarMeasure.integral_mul_left
    (fun U => (∑ i, hY.eigenvalues i * entry s U i) ^ 3) hY.eigenvectorUnitary⁻¹]
  rw [UnitaryProjectionGeneralCubic.integral_weighted_cube s hr]
  have h₁ := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 1
  simp only [pow_one] at h₁
  rw [cubicValue, h₁, HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 2,
    HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 3]
  rfl

theorem moment_three_complex (s : Finset κ) (hr : 3 ≤ Fintype.card κ)
    (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    UnitaryProjectionMoments.moment s Y 3 =
      cubicValue (Fintype.card κ) s.card (Matrix.trace Y)
        (Matrix.trace (Y ^ 2)) (Matrix.trace (Y ^ 3)) := by
  rw [moment_eq_integral_real s Y hY, integral_trace_cube s hr Y hY]
  change (algebraMap ℝ ℂ) (cubicValue (Fintype.card κ) s.card
    (Matrix.trace Y).re (Matrix.trace (Y ^ 2)).re (Matrix.trace (Y ^ 3)).re) = _
  simp only [cubicValue, Algebra.algebraMap_self_apply, map_add, map_mul, map_pow]
  have ht (Z : Matrix κ κ ℂ) (hZ : Z.IsHermitian) :
      (algebraMap ℝ ℂ) (Matrix.trace Z).re = Matrix.trace Z := by
    simpa using ofReal_re_trace Z hZ
  rw [ht Y hY, ht (Y ^ 2) (hY.pow 2), ht (Y ^ 3) (hY.pow 3)]

variable {S : Type*} [CommRing S] [Algebra ℂ S]

private theorem eval_trace_one (Y : Matrix κ κ S) :
    aeval (fun a : κ × κ => Y a.1 a.2)
      (Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ))) =
      Matrix.trace Y := by
  simpa only [pow_one] using GaussianQuadraticPolynomial.eval_universal_trace_pow Y 1

private theorem eval_cubic (r ell : ℝ) (Z : Matrix κ κ S) :
    aeval (fun a => Z a.1 a.2)
      (cubicValue r ell (Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ)))
        (Matrix.trace (GaussianQuadraticPolynomial.universalMatrix ^ 2))
        (Matrix.trace (GaussianQuadraticPolynomial.universalMatrix ^ 3))) =
      cubicValue r ell (Matrix.trace Z) (Matrix.trace (Z ^ 2)) (Matrix.trace (Z ^ 3)) := by
  simp only [cubicValue, map_add, map_mul, map_pow,
    GaussianQuadraticPolynomial.eval_universal_trace_pow, eval_trace_one,
    IsScalarTower.algebraMap_apply ℝ ℂ (MvPolynomial (κ × κ) ℂ),
    IsScalarTower.algebraMap_apply ℝ ℂ S]
  simp

theorem moment_three (s : Finset κ) (hr : 3 ≤ Fintype.card κ)
    (Y : Matrix κ κ S) :
    UnitaryProjectionMoments.moment s Y 3 =
      cubicValue (Fintype.card κ) s.card (Matrix.trace Y)
        (Matrix.trace (Y ^ 2)) (Matrix.trace (Y ^ 3)) := by
  let X : Matrix κ κ (MvPolynomial (κ × κ) ℂ) := GaussianQuadraticPolynomial.universalMatrix
  let p : MvPolynomial (κ × κ) ℂ :=
    cubicValue (Fintype.card κ) s.card (Matrix.trace X)
      (Matrix.trace (X ^ 2)) (Matrix.trace (X ^ 3))
  rw [UniversalProjectionMatrixMoments.extend_moment_identity s 3 p ?_ Y]
  · exact eval_cubic _ _ Y
  · intro A hA
    exact (moment_three_complex s hr A hA).trans (eval_cubic _ _ A).symm

end
end QuaternionicSymmetry.UniversalProjectionGeneralCubic
