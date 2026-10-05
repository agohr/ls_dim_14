import QuaternionicSymmetry.QuaternionicManifoldStandardP1Normalization
import QuaternionicSymmetry.ManifoldQuaternionicSymplecticTraceClass

/-! A global closed analytic standard trace-square form assembled from the
already glued tangent and rank-three Chern–Weil forms. Its chart expression
is the curvature trace of the actual standard representation. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicStandardTraceClass

open ManifoldDifferentialForms ManifoldDeRhamRing ManifoldDeRhamWedge
  ManifoldQuaternionicSymplecticTraceClass
  ManifoldQuaternionicAdjointChernWeil
  ManifoldQuaternionicAdjointChernWeilIndependence
  QuaternionicManifoldStandardTraceSquare
  QuaternionicManifoldStandardP1Normalization
  ManifoldQuaternionicConnection
  LocalEndomorphismTrace LocalChernWeilQuadratic
open scoped ContDiff Manifold Topology Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def closedStandardTraceSquare : closedForms (E := E) (M₀ := M) 4 :=
  closedSymplecticTraceSquare Q D +
    (1 / 2 : ℝ) • closedTraceCurvatureSquare Q D

theorem closedStandardTraceSquare_chart (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inChartModel p (closedStandardTraceSquare Q D).val.val y =
      traceSquareForm traceCLM
        (QuaternionicManifoldProjectiveStandardConnection.standardConnection S Q D p) y := by
  change inChartModel p
      ((closedSymplecticTraceSquare Q D).val.val +
        (1 / 2 : ℝ) • (closedTraceCurvatureSquare Q D).val.val) y = _
  rw [inChartModel_add, inChartModel_smul]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [closedSymplecticTraceSquare_chart Q D p y hy]
  change traceSquareForm traceCLM
      (ManifoldQuaternionicConnectionSplitting.symplecticConnection Q D p) y +
      (1 / 2 : ℝ) • inChartModel p (traceCurvatureSquare Q D) y = _
  rw [traceCurvatureSquare_chart Q D p hy]
  simp only [LocalChernWeilTracePowers.traceCurvaturePowerForm,
    LocalChernWeilTracePowers.tracePowerForm_one_eq_traceSquareForm]
  exact (standard_traceSquareForm S Q D p y hy).symm

def closedStandardP1 : closedForms (E := E) (M₀ := M) 4 :=
  (1 / (16 * Real.pi ^ 2) : ℝ) • closedStandardTraceSquare Q D

theorem closedStandardP1_chart (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inChartModel p (closedStandardP1 Q D).val.val y =
      standardP1Local S Q D p y := by
  change inChartModel p
      ((1 / (16 * Real.pi ^ 2) : ℝ) •
        (closedStandardTraceSquare Q D).val.val) y = _
  rw [inChartModel_smul]
  simp only [Pi.smul_apply]
  rw [closedStandardTraceSquare_chart S Q D p y hy]
  rfl

def closedTangentHalfP1 : closedForms (E := E) (M₀ := M) 4 :=
  (1 / (16 * Real.pi ^ 2) : ℝ) • closedTangentTraceSquare Q D

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
theorem closedStandardP1_eq_recoveredCandidate :
    closedStandardP1 Q D = closedTangentHalfP1 Q D +
      ((S.quaternionicDimension : ℝ) - 1) •
        quarterPontryaginCandidateForm Q D := by
  unfold closedStandardP1 closedStandardTraceSquare
    closedTangentHalfP1 closedSymplecticTraceSquare
    quarterPontryaginCandidateForm
  have hn : (Module.finrank ℝ E : ℝ) =
      4 * (S.quaternionicDimension : ℝ) := by exact_mod_cast S.real_finrank
  rw [hn]
  module

def standardP1Class : positiveDegreeCohomology (E := E) (M₀ := M) 3 :=
  closedFormClassHom 3 (closedStandardP1 Q D)

set_option synthInstance.maxHeartbeats 100000 in
theorem standardP1Class_eq_recoveredCandidate :
    standardP1Class Q D =
      (1 / (16 * Real.pi ^ 2) : ℝ) •
        (closedFormClassHom 3 (closedTangentTraceSquare Q D)) +
      ((S.quaternionicDimension : ℝ) - 1) •
        quarterPontryaginCandidateClass Q D := by
  rw [standardP1Class, closedStandardP1_eq_recoveredCandidate S Q D]
  rw [map_add]
  change closedFormClass 3 (closedTangentHalfP1 Q D) +
      closedFormClass 3
        (((S.quaternionicDimension : ℝ) - 1) • quarterPontryaginCandidateForm Q D) = _
  rw [closedTangentHalfP1, closedFormClass_smul,
    closedFormClass_smul]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
theorem standardP1Class_connection_independent
    (D' : CompatibleTangentConnection Q) :
    standardP1Class Q D' = standardP1Class Q D := by
  unfold standardP1Class closedStandardP1 closedStandardTraceSquare
  change closedFormClass 3
      ((1 / (16 * Real.pi ^ 2) : ℝ) •
        (closedSymplecticTraceSquare Q D' +
          (1 / 2 : ℝ) • closedTraceCurvatureSquare Q D')) =
    closedFormClass 3
      ((1 / (16 * Real.pi ^ 2) : ℝ) •
        (closedSymplecticTraceSquare Q D +
          (1 / 2 : ℝ) • closedTraceCurvatureSquare Q D))
  rw [closedFormClass_smul, closedFormClass_smul]
  change (1 / (16 * Real.pi ^ 2) : ℝ) •
      closedFormClassHom 3
        (closedSymplecticTraceSquare Q D' +
          (1 / 2 : ℝ) • closedTraceCurvatureSquare Q D') =
    (1 / (16 * Real.pi ^ 2) : ℝ) •
      closedFormClassHom 3
        (closedSymplecticTraceSquare Q D +
          (1 / 2 : ℝ) • closedTraceCurvatureSquare Q D)
  rw [map_add, map_add]
  change (1 / (16 * Real.pi ^ 2) : ℝ) •
      (closedFormClass 3 (closedSymplecticTraceSquare Q D') +
        closedFormClass 3 ((1 / 2 : ℝ) • closedTraceCurvatureSquare Q D')) =
    (1 / (16 * Real.pi ^ 2) : ℝ) •
      (closedFormClass 3 (closedSymplecticTraceSquare Q D) +
        closedFormClass 3 ((1 / 2 : ℝ) • closedTraceCurvatureSquare Q D))
  rw [closedFormClass_smul, closedFormClass_smul]
  change (1 / (16 * Real.pi ^ 2) : ℝ) •
      (symplecticTraceSquareClass Q D' +
        (1 / 2 : ℝ) • traceCurvatureSquareClass Q D') =
    (1 / (16 * Real.pi ^ 2) : ℝ) •
      (symplecticTraceSquareClass Q D +
        (1 / 2 : ℝ) • traceCurvatureSquareClass Q D)
  rw [symplecticTraceSquareClass_connection_independent Q D D',
    traceCurvatureSquareClass_eq Q D D']

end
end QuaternionicSymmetry.ManifoldQuaternionicStandardTraceClass
