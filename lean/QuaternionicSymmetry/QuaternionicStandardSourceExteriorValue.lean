import QuaternionicSymmetry.QuaternionicActualSymplecticTraceForms
import QuaternionicSymmetry.QuaternionicNormalizedTangentScale
import QuaternionicSymmetry.QuaternionicStandardTracePowerBlocks
import QuaternionicSymmetry.QuaternionicClosedSourceGenerators
import QuaternionicSymmetry.QuaternionicScalarLineTracePowerForm
import QuaternionicSymmetry.QuaternionicActualNormalizedRootIdentity

namespace QuaternionicSymmetry.QuaternionicStandardSourceExteriorValue
open QuaternionicActualSymplecticTraceForms
  QuaternionicNormalizedTangentScale
  QuaternionicActualSpCurvatureCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicTangentUniversalSpecialization
  QuaternionicExteriorEvenTrace QuaternionicUniversalEvenTrace
  QuaternionicCurvatureExteriorCoordinates
  QuaternionicScalarLineTracePowerForm
  QuaternionicActualNormalizedRootIdentity
  QuaternionicStandardTracePowerBlocks
  QuaternionicManifoldProjectiveStandardConnection
  HomogeneousMatrixCombinations
  QuaternionicClosedSourceGenerators
  QuaternionicCorrectedSourceTraceForms
  QuaternionicManifoldCorrectedTracePowers
  QuaternionicManifoldCorrectedConnection
  ExteriorMatrixWedgeBridge ExteriorMatrixTraceBridge
  ExteriorContinuousPairing ManifoldFormExteriorEvaluation
  ManifoldEvenClosedEvaluation ManifoldEvenClosedAlgebra
  ManifoldDeRhamAllDegrees ManifoldDeRhamRing ManifoldDeRhamWedge
  ManifoldDifferentialForms LocalChernWeilTracePowers
  ContinuousAlgebraWedgePowers
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem standard_tracePowerForm_exterior (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (k : ℕ) :
    tracePowerForm LocalEndomorphismTrace.traceCLM
      (standardConnection S Q D p) k y =
    toContinuous (powerDegree k)
      (wedgeTrace (spMatrix (chartStructure Q p) (actualEta Q D p y))
        (formal_sp_entries_two (chartStructure Q p) (actualEta Q D p y)
          (actualEta_entries_two Q D p y)) k) +
    toContinuous (powerDegree k)
      (wedgeTrace (lineMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i)))
        (QuaternionicScalarLineExteriorCurvature.line_entries_two
          (fun i => axialCurvaturePower Q D p y i)) k) := by
  rw [standard_tracePowerForm_actual_blocks S Q D p y hy k,
    symplectic_tracePowerForm_eq_formal Q D p y hy k,
    scalarLine_tracePower_eq_exterior Q D p y k]

end
end QuaternionicSymmetry.QuaternionicStandardSourceExteriorValue
