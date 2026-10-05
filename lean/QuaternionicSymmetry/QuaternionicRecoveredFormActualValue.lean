import QuaternionicSymmetry.ManifoldClosedRecoveredPointwise
import QuaternionicSymmetry.QuaternionicNormalizedTangentScale
import QuaternionicSymmetry.QuaternionicActualNormalizedRootIdentity

/-! The actual global reconstructed forms evaluate to the exact normalized
Sp-plus-scalar root expression, without a spectrum or splitting assumption. -/
namespace QuaternionicSymmetry.QuaternionicRecoveredFormActualValue
open ManifoldClosedRecoveredClassComparison ManifoldClosedRecoveredPointwise
open ManifoldEvenClosedEvaluation QuaternionicRootRecoveryNaturality
open QuaternionicActualSpCurvatureCoordinates QuaternionicActualTangentExteriorMatrix
open QuaternionicTangentUniversalSpecialization QuaternionicTangentFormalMatrix
open QuaternionicScaledBinomialNormalization QuaternionicNormalizedTangentScale
open QuaternionicQuarterUExteriorValue QuaternionicActualNormalizedRootIdentity
open QuaternionicExteriorEvenTrace
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem recoveredForm_actual_value (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (j : Fin 7) :
    gradeValue p y (ContinuousLinearMap.id ℝ E) j.val
      (recoveredForm Q D (chartStructure Q p).quaternionicDimension j) =
    (-1 : EvenAlgebra E)^j.val *
      (scaledSpPower (algebraMap ℝ (EvenAlgebra E) normalization)
        (spMatrix (chartStructure Q p) (actualEta Q D p y)) j.val +
       (scaledU (algebraMap ℝ (EvenAlgebra E) normalization)
         (scalarNorm (chartStructure Q p) (actualEta Q D p y)))^j.val) := by
  rw [recoveredForm_value, quarterU_gradeValue Q D p y hy]
  change QuaternionicTangentRootConversion.recoveredStandardPower _
    (scaledU (algebraMap ℝ (EvenAlgebra E) normalization) _)
    (tangentValues Q D p y (ContinuousLinearMap.id ℝ E) _) j = _
  rw [← actual_recovered_standard Q D p y (algebraMap ℝ (EvenAlgebra E) normalization) j]
  apply recoveredStandardPower_congr_positive
  intro m hm _
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact normalizedTangentGrade_scaled Q D p y hy k

end
end QuaternionicSymmetry.QuaternionicRecoveredFormActualValue
