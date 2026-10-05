import QuaternionicSymmetry.QuaternionicActualNormSquareTrace
import QuaternionicSymmetry.ManifoldEvenClosedEvaluation
import QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeil

/-! The actual global closed quarter-rank-three trace class evaluates
to the scalar quaternionic root square in a fixed adapted chart. -/
namespace QuaternionicSymmetry.QuaternionicQuarterUExteriorValue
open QuaternionicActualNormSquareTrace
  QuaternionicActualNormalizedRootIdentity
  QuaternionicActualSpCurvatureCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicTangentUniversalSpecialization
  QuaternionicUniversalEvenTrace QuaternionicExteriorEvenTrace
  QuaternionicCurvatureExteriorCoordinates QuaternionicAdjointTracePowerForm
  QuaternionicAdjointExteriorCurvature
  ManifoldEvenClosedEvaluation ManifoldEvenClosedAlgebra
  ManifoldFormExteriorEvaluation ManifoldQuaternionicAdjointChernWeil
  ManifoldDifferentialForms LocalChernWeilTracePowers
  ExteriorContinuousPairing ExteriorMatrixTraceBridge
  EvenForms
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

def normalization : ℝ := 1 / (2 * Real.pi) ^ 2

theorem normalization_eq :
    normalization = 1 / (4 * Real.pi ^ 2) := by
  unfold normalization
  ring

theorem quarterU_gradeValue (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    gradeValue p y (ContinuousLinearMap.id ℝ E) 1
      (quarterPontryaginCandidateForm Q D) =
    algebraMap ℝ (EvenAlgebra E) normalization *
      scalarNorm (chartStructure Q p) (actualEta Q D p y) := by
  apply Subtype.ext
  change value p y (ContinuousLinearMap.id ℝ E) 4
    (quarterPontryaginCandidateForm Q D).val.val = _
  have hpair := induced_tracePowerForm_eq_exterior Q D p y hy 1
  have hchart := traceCurvatureSquare_chart Q D p hy
  have hlocal : localForm p y (ContinuousLinearMap.id ℝ E) 4
      (quarterPontryaginCandidateForm Q D).val.val =
      (-(1 / (32 * Real.pi ^ 2)) : ℝ) •
        toContinuous 4
          (wedgeTrace
            (adjointMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i)))
            (adjoint_entries_two (fun i => axialCurvaturePower Q D p y i)) 1) := by
    apply ContinuousAlternatingMap.ext
    intro w
    change inChartModel p
      ((-(1 / (32 * Real.pi ^ 2)) : ℝ) • traceCurvatureSquare Q D) y
        (fun i => (ContinuousLinearMap.id ℝ E) (w i)) = _
    simp only [ContinuousLinearMap.id_apply, inChartModel_smul,
      Pi.smul_apply, ContinuousAlternatingMap.smul_apply]
    rw [hchart]
    change (-(1 / (32 * Real.pi ^ 2)) : ℝ) •
      (tracePowerForm LocalEndomorphismTrace.traceCLM
        (ManifoldQuaternionicAdjointConnection.inducedForm Q D p) 1 y) w = _
    rw [hpair]
    rfl
  have hr : representative p y (ContinuousLinearMap.id ℝ E) 4
      (quarterPontryaginCandidateForm Q D).val.val =
      (-(1 / (32 * Real.pi ^ 2)) : ℝ) •
        wedgeTrace
          (adjointMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i)))
          (adjoint_entries_two (fun i => axialCurvaturePower Q D p y i)) 1 := by
    apply toContinuous_injective
    rw [representative_pairing, toContinuous_smul]
    exact hlocal
  rw [show value p y (ContinuousLinearMap.id ℝ E) 4
    (quarterPontryaginCandidateForm Q D).val.val =
      (representative p y (ContinuousLinearMap.id ℝ E) 4
        (quarterPontryaginCandidateForm Q D).val.val :
        ExteriorAlgebra ℝ (Module.Dual ℝ E)) from rfl]
  rw [hr]
  change (-(1 / (32 * Real.pi ^ 2)) : ℝ) •
      ((Matrix.trace
        (adjointMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i)) ^ 2) :
        EvenAlgebra E) : ExteriorAlgebra ℝ (Module.Dual ℝ E)) = _
  rw [adjoint_traceSquare_eq_scalarNorm Q D p y]
  have hc : (-(1 / (32 * Real.pi ^ 2)) : ℝ) * (-8) =
      normalization := by
    rw [normalization_eq]
    ring
  change (-(1 / (32 * Real.pi ^ 2)) : ℝ) •
      (-((8 : EvenAlgebra E) : ExteriorAlgebra ℝ (Module.Dual ℝ E)) *
        ((scalarNorm (chartStructure Q p) (actualEta Q D p y) :
          EvenAlgebra E) : ExteriorAlgebra ℝ (Module.Dual ℝ E))) = _
  rw [Algebra.smul_def]
  have h8 : -((8 : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) =
      algebraMap ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ E)) (-8) := by
    simp only [map_neg, map_ofNat]
    rfl
  rw [h8]
  have hrhs :
      ((algebraMap ℝ (EvenAlgebra E) normalization *
        scalarNorm (chartStructure Q p) (actualEta Q D p y) :
          EvenAlgebra E) : ExteriorAlgebra ℝ (Module.Dual ℝ E)) =
      algebraMap ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ E)) normalization *
        ((scalarNorm (chartStructure Q p) (actualEta Q D p y) :
          EvenAlgebra E) : ExteriorAlgebra ℝ (Module.Dual ℝ E)) := rfl
  rw [hrhs]
  rw [← mul_assoc, ← map_mul, hc]

end
end QuaternionicSymmetry.QuaternionicQuarterUExteriorValue
