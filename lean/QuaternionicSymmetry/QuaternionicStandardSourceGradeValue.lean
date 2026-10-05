import QuaternionicSymmetry.QuaternionicStandardSourceExteriorValue
import QuaternionicSymmetry.QuaternionicActualSymplecticTraceForms
import QuaternionicSymmetry.QuaternionicNormalizedTangentScale
import QuaternionicSymmetry.QuaternionicStandardTracePowerBlocks
import QuaternionicSymmetry.QuaternionicClosedSourceGenerators
import QuaternionicSymmetry.QuaternionicScalarLineTracePowerForm
import QuaternionicSymmetry.QuaternionicActualNormalizedRootIdentity

namespace QuaternionicSymmetry.QuaternionicStandardSourceGradeValue
open QuaternionicStandardSourceExteriorValue
  QuaternionicActualSymplecticTraceForms
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

theorem sourceGrade_zero_value (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (k : ℕ) :
    gradeValue p y (ContinuousLinearMap.id ℝ E) (k+1)
      (sourceGrade S Q D 0 k) =
    algebraMap ℝ (EvenAlgebra E)
      ((1/(2*Real.pi))^(2*(k+1))/4) *
      (Matrix.trace ((spMatrix (chartStructure Q p) (actualEta Q D p y))^(2*(k+1))) +
        Matrix.trace ((lineMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i))) ^
          (2*(k+1)))) := by
  let B := spMatrix (chartStructure Q p) (actualEta Q D p y)
  let C := lineMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i))
  let hB := formal_sp_entries_two (chartStructure Q p) (actualEta Q D p y)
    (actualEta_entries_two Q D p y)
  let hC := QuaternionicScalarLineExteriorCurvature.line_entries_two
    (fun i => axialCurvaturePower Q D p y i)
  let j := k+1
  let d := 2*j-1
  let a : ℝ := (1/(2*Real.pi))^(2*j)/4
  have hchart := (traceAtlas S Q D 0 d).globalForm_chart p hy
  have hstd := standard_tracePowerForm_exterior S Q D p y hy d
  have hlocal : inChartModel p (closedSourceEvenTrace S Q D 0 j).val.val y =
      a • (toContinuous (powerDegree d) (wedgeTrace B hB d) +
        toContinuous (powerDegree d) (wedgeTrace C hC d)) := by
    change inChartModel p (a • (traceAtlas S Q D 0 d).globalForm) y = _
    rw [inChartModel_smul, Pi.smul_apply, hchart]
    change a • tracePowerForm LocalEndomorphismTrace.traceCLM
      (correctedConnection S Q D 0 p) d y = _
    have h0 : correctedConnection S Q D 0 p = standardConnection S Q D p := by
      funext x
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro z
      change standardConnection S Q D p x u z +
        (0 : ℝ) • QuaternionicManifoldStandardSolder.standardSolder S Q p x u z = _
      rw [zero_smul, add_zero]
    rw [h0, hstd]
  have hrep : representative p y (ContinuousLinearMap.id ℝ E)
      (powerDegree d) (closedSourceEvenTrace S Q D 0 j).val.val =
      a • (wedgeTrace B hB d + wedgeTrace C hC d) := by
    apply toContinuous_injective
    rw [representative_pairing, toContinuous_smul, toContinuous_add]
    apply ContinuousAlternatingMap.ext
    intro v
    change inChartModel p (closedSourceEvenTrace S Q D 0 j).val.val y
      (fun i => (ContinuousLinearMap.id ℝ E) (v i)) = _
    simpa only [ContinuousLinearMap.id_apply] using
      congrArg (fun z : E [⋀^Fin (powerDegree d)]→L[ℝ] ℝ => z v) hlocal
  apply Subtype.ext
  change value p y (ContinuousLinearMap.id ℝ E) (4*k+4)
    (castClosedDegree (sourceDegree k) (closedSourceEvenTrace S Q D 0 j)).val.val = _
  rw [castClosedDegree_form, value_cast]
  change (representative p y (ContinuousLinearMap.id ℝ E)
      (powerDegree d) (closedSourceEvenTrace S Q D 0 j).val.val :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) = _
  rw [hrep]
  change ((a • (Matrix.trace (B ^ (d+1)) + Matrix.trace (C ^ (d+1))) :
      EvenAlgebra E) : ExteriorAlgebra ℝ (Module.Dual ℝ E)) = _
  congr 1

end
end QuaternionicSymmetry.QuaternionicStandardSourceGradeValue
