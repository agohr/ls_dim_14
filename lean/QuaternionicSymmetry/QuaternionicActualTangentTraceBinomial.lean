import QuaternionicSymmetry.QuaternionicActualFullExteriorMatrix
import QuaternionicSymmetry.ContinuousEndomorphismExteriorTrace

/-! All-degree actual tangent trace forms have the formal Sp-plus-scalar
exterior matrix representative. The universal binomial then holds in the
commutative algebra of actual even exterior coefficients. -/
namespace QuaternionicSymmetry.QuaternionicActualTangentTraceBinomial
open QuaternionicActualSpCurvatureCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicActualFullExteriorMatrix
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

theorem tangent_exteriorMatrix_eq_formal (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    exteriorEndomorphismMatrix (Module.finBasis ℝ E)
      (curvatureForm (D.form p) y) =
    spMatrix (chartStructure Q p) (actualEta Q D p y) +
      scalarMatrix (chartStructure Q p) (actualEta Q D p y) := by
  let S := chartStructure Q p
  let η := actualEta Q D p y
  let hsp := formal_sp_entries_two S η (actualEta_entries_two Q D p y)
  let hsc := formal_scalar_entries_two S η (actualEta_entries_two Q D p y)
  let hfull := entries_two_add _ _ hsp hsc
  have h := actual_tangent_matrixTwoForm Q D p y hy
  have hinv := exteriorMatrix_matrixTwoForm (spMatrix S η + scalarMatrix S η) hfull
  change exteriorMatrix ((matrixCLM (Module.finBasis ℝ E)).compContinuousAlternatingMap
    (curvatureForm (D.form p) y)) = _
  rw [← h]
  exact hinv

theorem symplectic_exteriorMatrix_eq_formal (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    exteriorEndomorphismMatrix (Module.finBasis ℝ E)
      (curvatureForm (symplecticConnection Q D p) y) =
    spMatrix (chartStructure Q p) (actualEta Q D p y) := by
  let S := chartStructure Q p
  let η := actualEta Q D p y
  let hsp := formal_sp_entries_two S η (actualEta_entries_two Q D p y)
  have h := actual_sp_matrixTwoForm Q D p y hy
  have hinv := exteriorMatrix_matrixTwoForm (spMatrix S η) hsp
  change exteriorMatrix ((matrixCLM (Module.finBasis ℝ E)).compContinuousAlternatingMap
    (curvatureForm (symplecticConnection Q D p) y)) = _
  rw [← h]
  exact hinv

theorem tangent_tracePowerForm_eq_formal (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (k : ℕ) :
    tracePowerForm LocalEndomorphismTrace.traceCLM (D.form p) k y =
      toContinuous (powerDegree k)
        (wedgeTrace
          (spMatrix (chartStructure Q p) (actualEta Q D p y) +
            scalarMatrix (chartStructure Q p) (actualEta Q D p y))
          (entries_two_add _ _
            (formal_sp_entries_two (chartStructure Q p) (actualEta Q D p y)
              (actualEta_entries_two Q D p y))
            (formal_scalar_entries_two (chartStructure Q p) (actualEta Q D p y)
              (actualEta_entries_two Q D p y))) k) := by
  let F := curvatureForm (D.form p) y
  let A := exteriorEndomorphismMatrix (Module.finBasis ℝ E) F
  let hA := entries_two ((matrixCLM (Module.finBasis ℝ E)).compContinuousAlternatingMap F)
  let S := chartStructure Q p
  let η := actualEta Q D p y
  let B := spMatrix S η + scalarMatrix S η
  let hB := entries_two_add _ _
    (formal_sp_entries_two S η (actualEta_entries_two Q D p y))
    (formal_scalar_entries_two S η (actualEta_entries_two Q D p y))
  have ht := trace_power_eq_exterior (Module.finBasis ℝ E) F k
  rw [power_curvatureForm] at ht
  change tracePowerForm LocalEndomorphismTrace.traceCLM (D.form p) k y =
    toContinuous (powerDegree k) (wedgeTrace A hA k) at ht
  calc
    tracePowerForm LocalEndomorphismTrace.traceCLM (D.form p) k y =
      toContinuous (powerDegree k) (wedgeTrace A hA k) := ht
    _ = toContinuous (powerDegree k) (wedgeTrace B hB k) := by
      exact congrArg (toContinuous (powerDegree k))
        (wedgeTrace_congr A B hA hB k
          (tangent_exteriorMatrix_eq_formal Q D p y hy))

theorem tangent_even_trace_formal_binomial (p : M) (y : E) (j : ℕ) :
    Matrix.trace ((spMatrix (chartStructure Q p) (actualEta Q D p y) +
      scalarMatrix (chartStructure Q p) (actualEta Q D p y)) ^ (2 * j)) =
    ∑ m ∈ Finset.range (2 * j + 1),
      (if Even (2 * j - m) then
        (-(scalarNorm (chartStructure Q p) (actualEta Q D p y))) ^
          ((2 * j - m) / 2) *
          Matrix.trace ((spMatrix (chartStructure Q p) (actualEta Q D p y)) ^ m)
       else 0) * (Nat.choose (2 * j) m : EvenAlgebra E) :=
  tangent_even_trace_specialized (chartStructure Q p) (actualEta Q D p y) j

end
end QuaternionicSymmetry.QuaternionicActualTangentTraceBinomial
