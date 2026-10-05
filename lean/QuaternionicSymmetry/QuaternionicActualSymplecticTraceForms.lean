import QuaternionicSymmetry.QuaternionicActualTangentTraceBinomial

/-! The actual symplectic block trace is the trace of its universal
homogeneous exterior matrix, at every positive curvature power. -/
namespace QuaternionicSymmetry.QuaternionicActualSymplecticTraceForms
open QuaternionicActualSpCurvatureCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicActualTangentTraceBinomial
  QuaternionicTangentUniversalSpecialization
  HomogeneousMatrixCombinations ContinuousMatrixExteriorInverse
  ContinuousMatrixExteriorEquivalence
  ContinuousEndomorphismExteriorTrace
  QuaternionicExteriorEvenTrace ExteriorMatrixWedgeBridge
  ExteriorMatrixTraceBridge ExteriorContinuousPairing
  ContinuousEndomorphismMatrix ContinuousAlgebraWedgePowers
  LocalChernWeilTracePowers LocalConnectionForms
  ManifoldQuaternionicConnectionSplitting
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem symplectic_tracePowerForm_eq_formal (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (k : ℕ) :
    tracePowerForm LocalEndomorphismTrace.traceCLM
      (symplecticConnection Q D p) k y =
    toContinuous (powerDegree k)
      (wedgeTrace (spMatrix (chartStructure Q p) (actualEta Q D p y))
        (formal_sp_entries_two (chartStructure Q p) (actualEta Q D p y)
          (actualEta_entries_two Q D p y)) k) := by
  let F := curvatureForm (symplecticConnection Q D p) y
  let A := exteriorEndomorphismMatrix (Module.finBasis ℝ E) F
  let hA := entries_two ((matrixCLM (Module.finBasis ℝ E)).compContinuousAlternatingMap F)
  let B := spMatrix (chartStructure Q p) (actualEta Q D p y)
  let hB := formal_sp_entries_two (chartStructure Q p) (actualEta Q D p y)
    (actualEta_entries_two Q D p y)
  have ht := trace_power_eq_exterior (Module.finBasis ℝ E) F k
  rw [power_curvatureForm] at ht
  change tracePowerForm LocalEndomorphismTrace.traceCLM
      (symplecticConnection Q D p) k y =
    toContinuous (powerDegree k) (wedgeTrace A hA k) at ht
  calc
    tracePowerForm LocalEndomorphismTrace.traceCLM
        (symplecticConnection Q D p) k y =
      toContinuous (powerDegree k) (wedgeTrace A hA k) := ht
    _ = toContinuous (powerDegree k) (wedgeTrace B hB k) := by
      exact congrArg (toContinuous (powerDegree k))
        (wedgeTrace_congr A B hA hB k
          (symplectic_exteriorMatrix_eq_formal Q D p y hy))

end
end QuaternionicSymmetry.QuaternionicActualSymplecticTraceForms
