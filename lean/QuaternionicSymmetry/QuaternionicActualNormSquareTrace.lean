import QuaternionicSymmetry.QuaternionicActualNormalizedRootIdentity
import QuaternionicSymmetry.QuaternionicAdjointTracePowerForm

/-! Exact scalar norm-square versus actual rank-three trace square in
the even exterior coefficient algebra; this fixes the 1/(4π²) class
normalization of the quaternionic line root. -/
namespace QuaternionicSymmetry.QuaternionicActualNormSquareTrace
open QuaternionicActualNormalizedRootIdentity
  QuaternionicActualSpCurvatureCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicTangentUniversalSpecialization
  QuaternionicUniversalEvenTrace QuaternionicExteriorEvenTrace
  QuaternionicCurvatureExteriorCoordinates EvenForms
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem adjoint_traceSquare_eq_scalarNorm (p : M) (y : E) :
    Matrix.trace
      (adjointMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i)) ^ 2) =
        -(8 : EvenAlgebra E) *
          scalarNorm (chartStructure Q p) (actualEta Q D p y) := by
  rw [adjointMatrix_even_trace _ 1 (by omega), scalarNorm_actualEta Q D p y]
  ring

end
end QuaternionicSymmetry.QuaternionicActualNormSquareTrace
