import QuaternionicSymmetry.ManifoldQuaternionicScalarTraceComparison
import QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeilIndependence
import QuaternionicSymmetry.ManifoldQuaternionicChernWeilIndependence
import QuaternionicSymmetry.ManifoldDeRhamRing

/-! The symplectic trace-square form is a genuine global closed form,
identified chartwise by the proved tangent/rank-three trace comparison. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicSymplecticTraceClass

open ManifoldDifferentialForms ManifoldDeRhamRing ManifoldDeRhamWedge
  ManifoldQuaternionicConnection ManifoldQuaternionicConnectionSplitting
  ManifoldQuaternionicScalarTraceComparison
  LocalEndomorphismTrace LocalChernWeilQuadratic LocalChernWeilTracePowers
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

def closedTangentTraceSquare : closedForms (E := E) (M₀ := M) 4 :=
  (ManifoldQuaternionicChernWeil.gaugeAtlas (Q := Q) (D := D) 1).toTracePowerAtlas.closedGlobalForm

def closedSymplecticTraceSquare : closedForms (E := E) (M₀ := M) 4 :=
  closedTangentTraceSquare Q D -
    ((Module.finrank ℝ E : ℝ) / 8) •
      ManifoldQuaternionicAdjointChernWeil.closedTraceCurvatureSquare Q D

theorem closedSymplecticTraceSquare_chart (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inChartModel p (closedSymplecticTraceSquare Q D).val.val y =
      traceSquareForm traceCLM (symplecticConnection Q D p) y := by
  have hT := (ManifoldQuaternionicChernWeil.gaugeAtlas (Q := Q) (D := D) 1).toTracePowerAtlas.globalForm_chart p hy
  change inChartModel p (closedTangentTraceSquare Q D).val.val y =
    traceCurvaturePowerForm (D.form p) 1 y at hT
  have hQ := ManifoldQuaternionicAdjointChernWeil.traceCurvatureSquare_chart Q D p hy
  change inChartModel p
      ((closedTangentTraceSquare Q D).val.val -
        ((Module.finrank ℝ E : ℝ) / 8) •
          ManifoldQuaternionicAdjointChernWeil.traceCurvatureSquare Q D) y = _
  rw [sub_eq_add_neg, ← neg_one_smul ℝ
    (((Module.finrank ℝ E : ℝ) / 8) •
      ManifoldQuaternionicAdjointChernWeil.traceCurvatureSquare Q D),
    inChartModel_add, inChartModel_smul, inChartModel_smul]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [hT, hQ]
  change tracePowerForm traceCLM (D.form p) 1 y +
      (-1 : ℝ) • (((Module.finrank ℝ E : ℝ) / 8) •
        tracePowerForm traceCLM (ManifoldQuaternionicAdjointConnection.inducedForm Q D p) 1 y) = _
  rw [tracePowerForm_one_eq_traceSquareForm, tracePowerForm_one_eq_traceSquareForm,
    tangent_traceSquareForm Q D p y hy]
  module

private def classFourHom : closedForms (E := E) (M₀ := M) 4 →+
    positiveDegreeCohomology (E := E) (M₀ := M) 3 := closedFormClassHom 3

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem classFourHom_smul (c : ℝ) (α : closedForms (E := E) (M₀ := M) 4) :
    classFourHom (c • α) = c • classFourHom α := closedFormClass_smul 3 c α

def symplecticTraceSquareClass : positiveDegreeCohomology (E := E) (M₀ := M) 3 :=
  classFourHom (closedSymplecticTraceSquare Q D)

theorem symplecticTraceSquareClass_connection_independent (D' : CompatibleTangentConnection Q) :
    symplecticTraceSquareClass Q D' = symplecticTraceSquareClass Q D := by
  have hT := ManifoldQuaternionicChernWeilIndependence.tracePowerClass_eq Q D D' 1
  have hQ := ManifoldQuaternionicAdjointChernWeilIndependence.traceCurvatureSquareClass_eq Q D D'
  unfold symplecticTraceSquareClass closedSymplecticTraceSquare
  rw [(classFourHom (E := E) (M := M)).map_sub,
    (classFourHom (E := E) (M := M)).map_sub]
  rw [classFourHom_smul, classFourHom_smul]
  exact congrArg₂ (fun a b : positiveDegreeCohomology (E := E) (M₀ := M) 3 =>
    a - ((Module.finrank ℝ E : ℝ) / 8) • b) hT hQ

end
end QuaternionicSymmetry.ManifoldQuaternionicSymplecticTraceClass
