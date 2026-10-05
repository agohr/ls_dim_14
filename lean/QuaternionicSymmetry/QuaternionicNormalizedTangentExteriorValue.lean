import QuaternionicSymmetry.QuaternionicQuarterUExteriorValue
import QuaternionicSymmetry.ManifoldClosedTangentGenerators
import QuaternionicSymmetry.QuaternionicActualTangentTraceBinomial

namespace QuaternionicSymmetry.QuaternionicNormalizedTangentExteriorValue
open QuaternionicActualSpCurvatureCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicActualTangentTraceBinomial
  QuaternionicTangentUniversalSpecialization
  HomogeneousMatrixCombinations ContinuousMatrixExteriorEquivalence
  QuaternionicExteriorEvenTrace ExteriorMatrixTraceBridge
  ExteriorContinuousPairing ManifoldFormExteriorEvaluation
  ManifoldEvenClosedEvaluation ManifoldEvenClosedAlgebra
  ManifoldClosedTangentGenerators
  ManifoldDifferentialForms ManifoldQuaternionicChernWeil
  ManifoldDeRhamRing
  ManifoldDeRhamWedge
  LocalChernWeilTracePowers
  LocalChernWeilOrderedTransgression
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem normalizedTangentGrade_value (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (k : ℕ) :
    gradeValue p y (ContinuousLinearMap.id ℝ E) (k+1)
      (normalizedTangentGrade Q D k) =
    algebraMap ℝ (EvenAlgebra E)
      (ManifoldTangentTraceRootCandidates.tangentTraceScale (k+1) *
        ((-1 : ℝ)^(k+1)/2)) *
      Matrix.trace ((spMatrix (chartStructure Q p) (actualEta Q D p y) +
        scalarMatrix (chartStructure Q p) (actualEta Q D p y)) ^ (2*(k+1))) := by
  let S := chartStructure Q p
  let η := actualEta Q D p y
  let A := spMatrix S η + scalarMatrix S η
  let hA := entries_two_add _ _
    (formal_sp_entries_two S η (actualEta_entries_two Q D p y))
    (formal_scalar_entries_two S η (actualEta_entries_two Q D p y))
  have hchart :=
    ((gaugeAtlas Q D (2*k+1)).toTracePowerAtlas).globalForm_chart p hy
  have htrace := tangent_tracePowerForm_eq_formal Q D p y hy (2*k+1)
  have hbase : representative p y (ContinuousLinearMap.id ℝ E)
      (powerDegree (2*k+1))
      ((gaugeAtlas Q D (2*k+1)).toTracePowerAtlas.closedGlobalForm).val.val =
      wedgeTrace A hA (2*k+1) := by
    apply toContinuous_injective
    rw [representative_pairing]
    apply ContinuousAlternatingMap.ext
    intro w
    change inChartModel p
      ((gaugeAtlas Q D (2*k+1)).toTracePowerAtlas.globalForm) y
      (fun i => (ContinuousLinearMap.id ℝ E) (w i)) = _
    simp only [ContinuousLinearMap.id_apply]
    rw [hchart]
    change (tracePowerForm LocalEndomorphismTrace.traceCLM
      (D.form p) (2*k+1) y) w = _
    exact congrArg (fun α : E [⋀^Fin (powerDegree (2*k+1))]→L[ℝ] ℝ => α w) htrace
  have hraw : gradeValue p y (ContinuousLinearMap.id ℝ E) (k+1)
      (castClosed (tangentDegree k)
        ((primitiveDegree_add_one (2*k+1)).symm ▸
          (gaugeAtlas Q D (2*k+1)).toTracePowerAtlas.closedGlobalForm)) =
      Matrix.trace (A ^ (2*(k+1))) := by
    apply Subtype.ext
    change value p y (ContinuousLinearMap.id ℝ E) (4*k+4)
      (castClosed (tangentDegree k)
        ((primitiveDegree_add_one (2*k+1)).symm ▸
          (gaugeAtlas Q D (2*k+1)).toTracePowerAtlas.closedGlobalForm)).val.val = _
    rw [castClosed_form, value_cast]
    have htransport {m n : ℕ} (h : m = n)
        (a : closedForms (E := E) (M₀ := M) m) :
        value p y (ContinuousLinearMap.id ℝ E) n (h ▸ a).val.val =
          value p y (ContinuousLinearMap.id ℝ E) m a.val.val := by
      cases h
      rfl
    rw [htransport]
    change (representative p y (ContinuousLinearMap.id ℝ E) (powerDegree (2*k+1))
      ((gaugeAtlas Q D (2*k+1)).toTracePowerAtlas.closedGlobalForm).val.val :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) = _
    rw [hbase]
    simp only [wedgeTrace]
    congr 1
  rw [normalizedTangentGrade, rawTangentGrade, map_smul, map_smul]
  rw [hraw]
  rw [smul_smul, Algebra.smul_def]

end
end QuaternionicSymmetry.QuaternionicNormalizedTangentExteriorValue
