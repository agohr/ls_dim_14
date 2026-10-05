import QuaternionicSymmetry.QuaternionicStandardSourceGradeValue

/-! The standard quaternionic line contributes four copies of its single
squared axial root to every even exterior trace. -/
namespace QuaternionicSymmetry.QuaternionicActualScalarLineTrace
open QuaternionicUniversalEvenTrace QuaternionicExteriorEvenTrace
  QuaternionicActualNormalizedRootIdentity
  QuaternionicCurvatureExteriorCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicActualSpCurvatureCoordinates
  QuaternionicTangentUniversalSpecialization
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem line_even_trace_actual (p : M) (y : E) (j : ℕ) :
    Matrix.trace ((lineMatrix (liftTwo
      (fun i => axialCurvaturePower Q D p y i))) ^ (2*j)) =
    4 * (-(scalarNorm (chartStructure Q p) (actualEta Q D p y))) ^ j := by
  rw [lineMatrix_even_trace, scalarNorm_actualEta]

end
end QuaternionicSymmetry.QuaternionicActualScalarLineTrace
