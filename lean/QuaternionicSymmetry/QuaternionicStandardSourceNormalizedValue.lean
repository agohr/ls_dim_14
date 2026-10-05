import QuaternionicSymmetry.QuaternionicActualScalarLineTrace

/-! Exact normalization of the genuine standard source forms.  The signs
come from the real curvature powers and the quarter trace, with the scalar
quaternionic line included. -/
namespace QuaternionicSymmetry.QuaternionicStandardSourceNormalizedValue
open QuaternionicScaledBinomialNormalization
open QuaternionicStandardSourceGradeValue QuaternionicActualScalarLineTrace
open QuaternionicActualSpCurvatureCoordinates QuaternionicActualTangentExteriorMatrix
open QuaternionicTangentUniversalSpecialization QuaternionicTangentFormalMatrix
open QuaternionicExteriorEvenTrace QuaternionicQuarterUExteriorValue
open QuaternionicClosedSourceGenerators ManifoldEvenClosedEvaluation
open scoped Manifold ContDiff
noncomputable section

private theorem normalized_trace {R κ : Type} [CommRing R] [Algebra ℚ R]
    [Fintype κ] [DecidableEq κ] (c z : R) (A : Matrix κ κ R) (j : ℕ) :
    c^j * algebraMap ℚ R (1/4) *
        (Matrix.trace (A^(2*j)) + 4 * (-z)^j) =
      (-1 : R)^j * (scaledSpPower c A j + (scaledU c z)^j) := by
  have hquarter : (4 : R) * algebraMap ℚ R (1/4) = 1 := by
    have h := map_mul (algebraMap ℚ R) (4 : ℚ) (1/4 : ℚ)
    norm_num at h
    simpa only [map_ofNat] using h.symm
  have hsign : (-1 : R)^j * (-1 : R)^j = 1 := by
    rw [← mul_pow]
    norm_num
  unfold scaledSpPower scaledU
  rw [neg_pow, neg_pow, mul_pow]
  linear_combination
    (c^j * (-1)^j * z^j) * hquarter -
      (c^j * algebraMap ℚ R (1/4) * Matrix.trace (A^(2*j))) * hsign

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem sourceGrade_zero_normalized (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (k : ℕ) :
    gradeValue p y (ContinuousLinearMap.id ℝ E) (k+1)
      (sourceGrade S Q D 0 k) =
    (-1 : EvenAlgebra E)^(k+1) *
      (scaledSpPower (algebraMap ℝ (EvenAlgebra E) normalization)
        (spMatrix (chartStructure Q p) (actualEta Q D p y)) (k+1) +
       (scaledU (algebraMap ℝ (EvenAlgebra E) normalization)
         (scalarNorm (chartStructure Q p) (actualEta Q D p y)))^(k+1)) := by
  rw [sourceGrade_zero_value S Q D p y hy k, line_even_trace_actual Q D p y (k+1)]
  have hscale : (1/(2*Real.pi))^(2*(k+1))/4 = normalization^(k+1) * (1/4 : ℝ) := by
    unfold normalization
    rw [pow_mul, one_div_pow]
    ring
  rw [hscale, map_mul, map_pow]
  have hquarter : algebraMap ℝ (EvenAlgebra E) (1/4 : ℝ) =
      algebraMap ℚ (EvenAlgebra E) (1/4 : ℚ) := by
    have hr : (algebraMap ℚ ℝ) (1/4 : ℚ) = (1/4 : ℝ) := by norm_num
    simpa only [hr] using
      (IsScalarTower.algebraMap_apply ℚ ℝ (EvenAlgebra E) (1/4 : ℚ)).symm
  rw [hquarter]
  exact normalized_trace _ _ _ _

end
end QuaternionicSymmetry.QuaternionicStandardSourceNormalizedValue
