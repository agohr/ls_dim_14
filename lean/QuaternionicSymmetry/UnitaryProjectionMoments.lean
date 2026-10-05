import QuaternionicSymmetry.UnitaryProjection
import QuaternionicSymmetry.HermitianPolynomialExt

/-! Actual Haar projection moments with coefficients in any commutative
complex algebra, including their positive-ray averaging theorem. -/

namespace QuaternionicSymmetry.UnitaryProjectionMoments

open Matrix MvPolynomial MeasureTheory

noncomputable section

variable {κ S T : Type*} [Fintype κ] [DecidableEq κ]
  [CommRing S] [Algebra ℂ S] [CommRing T] [Algebra ℂ T]

def tracePolynomial (s : Finset κ) (Y : Matrix κ κ S) :
    MvPolynomial (UnitaryPolynomialExpectation.Variables κ) S :=
  Matrix.trace ((UnitaryProjection.matrixPolynomial s).map
    (MvPolynomial.map (algebraMap ℂ S)) * Y.map MvPolynomial.C)

def moment (s : Finset κ) (Y : Matrix κ κ S) (k : ℕ) : S :=
  UnitaryPolynomialExpectation.expectation (tracePolynomial s Y ^ k)

theorem eval_tracePolynomial (s : Finset κ) (Y : Matrix κ κ S)
    (U : Matrix.unitaryGroup κ ℂ) :
    (tracePolynomial s Y).eval
      (fun p => algebraMap ℝ S (UnitaryPolynomialExpectation.coordinates U p)) =
        Matrix.trace ((UnitaryProjection.projection s U).map (algebraMap ℂ S) * Y) := by
  unfold tracePolynomial
  rw [AddMonoidHom.map_trace, Matrix.map_mul]
  apply congrArg Matrix.trace
  congr 1
  · rw [← UnitaryProjection.eval_matrixPolynomial s U]
    ext i j
    simp only [Matrix.map_apply, MvPolynomial.eval_map]
    exact (MvPolynomial.eval₂_comp (algebraMap ℂ S)
      (fun p => (UnitaryPolynomialExpectation.coordinates U p : ℂ)) _).symm
  · ext i j
    simp

theorem moment_mul_contains {v w : S} (hv : v ≠ 0)
    (s : Finset κ) (Y : Matrix κ κ S) (k : ℕ)
    (h : ∀ U : Matrix.unitaryGroup κ ℂ,
      PositiveRay.Contains v
        (Matrix.trace ((UnitaryProjection.projection s U).map (algebraMap ℂ S) * Y) ^ k * w)) :
    PositiveRay.Contains v (moment s Y k * w) := by
  have hp := UnitaryPolynomialExpectation.expectation_contains hv
    (MvPolynomial.C w * tracePolynomial s Y ^ k) ?_
  · have hc (p : MvPolynomial (UnitaryPolynomialExpectation.Variables κ) S) :
        UnitaryPolynomialExpectation.expectation (MvPolynomial.C w * p) =
          w * UnitaryPolynomialExpectation.expectation p := by
      simpa only [MvPolynomial.smul_eq_C_mul, smul_eq_mul] using
        (UnitaryPolynomialExpectation.expectation (κ := κ) (S := S)).map_smul w p
    rw [hc] at hp
    change PositiveRay.Contains v (w * moment s Y k) at hp
    rwa [mul_comm w] at hp
  · intro U
    rw [map_mul, MvPolynomial.eval_C, map_pow, eval_tracePolynomial, mul_comm w]
    exact h U

theorem scalar_integrable (s : Finset κ) (Y : Matrix κ κ S) (k : ℕ) (L : S →ₗ[ℝ] ℝ) :
    Integrable (fun U : Matrix.unitaryGroup κ ℂ =>
      L (Matrix.trace ((UnitaryProjection.projection s U).map (algebraMap ℂ S) * Y) ^ k))
        UnitaryHaarMeasure.probability := by
  simpa only [map_pow, eval_tracePolynomial] using
    UnitaryPolynomialExpectation.polynomial_integrable L (tracePolynomial s Y ^ k)

theorem integral_scalar (s : Finset κ) (Y : Matrix κ κ S) (k : ℕ) (L : S →ₗ[ℝ] ℝ) :
    (∫ U : Matrix.unitaryGroup κ ℂ,
      L (Matrix.trace ((UnitaryProjection.projection s U).map (algebraMap ℂ S) * Y) ^ k)
        ∂UnitaryHaarMeasure.probability) = L (moment s Y k) := by
  simpa only [map_pow, eval_tracePolynomial, moment] using
    UnitaryPolynomialExpectation.integral_polynomial L (tracePolynomial s Y ^ k)

theorem scalar_mixed_integrable (s : Finset κ) (Y : Matrix κ κ S) (k : ℕ)
    (w : S) (L : S →ₗ[ℝ] ℝ) :
    Integrable (fun U : Matrix.unitaryGroup κ ℂ =>
      L (Matrix.trace ((UnitaryProjection.projection s U).map (algebraMap ℂ S) * Y) ^ k * w))
        UnitaryHaarMeasure.probability :=
  scalar_integrable s Y k (L.comp (LinearMap.mulRight ℝ w))

theorem integral_scalar_mixed (s : Finset κ) (Y : Matrix κ κ S) (k : ℕ)
    (w : S) (L : S →ₗ[ℝ] ℝ) :
    (∫ U : Matrix.unitaryGroup κ ℂ,
      L (Matrix.trace ((UnitaryProjection.projection s U).map (algebraMap ℂ S) * Y) ^ k * w)
        ∂UnitaryHaarMeasure.probability) = L (moment s Y k * w) :=
  integral_scalar s Y k (L.comp (LinearMap.mulRight ℝ w))

end
end QuaternionicSymmetry.UnitaryProjectionMoments
