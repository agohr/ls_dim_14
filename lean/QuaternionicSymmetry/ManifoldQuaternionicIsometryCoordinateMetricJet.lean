import QuaternionicSymmetry.GeneralLeviCivitaMetricIsometryJetCalculus
import QuaternionicSymmetry.ManifoldQuaternionicIsometryChartFields
import QuaternionicSymmetry.ManifoldQuaternionicCoordinateMetricity

/-! The differentiated metric covariance of an actual smooth isometry in
adapted chart coordinates, at the center of a fixed source chart. It uses
the checked solder field and symmetric second derivative of the chart map;
no connection-invariance or quaternionic-parallelism premise occurs. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryCoordinateMetricJet

open Filter
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryChartFields
open GeneralLeviCivitaMetricIsometryJetCalculus
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateMetric_isometry_first_jet_center
    (f : QuaternionicIsometries Q) (p : M) (u v w : E) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    let F := localIsometryChartMap Q f p
    let R := fderiv ℝ F
    let dR := fderiv ℝ R y₀
    fderiv ℝ (fun z => coordinateMetric Q p z v w) y₀ u =
      fderiv ℝ (fun z => coordinateMetric Q (f • p) z (R y₀ v) (R y₀ w))
        (F y₀) (R y₀ u) +
      coordinateMetric Q (f • p) (F y₀) (dR u v) (R y₀ w) +
      coordinateMetric Q (f • p) (F y₀) (R y₀ v) (dR u w) := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let F := localIsometryChartMap Q f p
  let R := fderiv ℝ F
  let T := solder Q (f • p)
  have hy : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hsrc : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hFy : F y₀ = extChartAt 𝓘(ℝ,E) (f • p) (f • p) := by
    simp only [F, localIsometryChartMap, hsrc]
  have htarget : F y₀ ∈ (extChartAt 𝓘(ℝ,E) (f • p)).target := by
    rw [hFy]
    exact (extChartAt 𝓘(ℝ,E) (f • p)).map_source (by simp)
  have hF : ContDiffAt ℝ 2 F y₀ :=
    localIsometryChartMap_contDiffAt_center Q f p
  have hT : DifferentiableAt ℝ T (F y₀) :=
    (ManifoldQuaternionicCoordinateSecondBianchi.solder_contDiffAt
      Q (f • p) (F y₀) htarget).differentiableAt (by norm_num)
  have hevent : (fun z => coordinateMetric Q p z v w) =ᶠ[𝓝 y₀]
      fun z => coordinateMetric Q (f • p) (F z) (R z v) (R z w) := by
    filter_upwards [localIsometryChart_overlap_eventually Q f p]
      with z hz
    exact ManifoldQuaternionicIsometryCoordinateMetric.coordinateMetric_isometry
      Q f p z hz.1 (by simpa only [extChartAt_source] using hz.2.2) v w
  have hder := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (hevent.fderiv_eq (𝕜 := ℝ))
  change fderiv ℝ (fun z => coordinateMetric Q p z v w) y₀ u =
    fderiv ℝ (fun z => inner ℝ (T (F z) (R z v)) (T (F z) (R z w))) y₀ u at hder
  rw [fderiv_inner_solder_chart_map F T y₀ u v w hF hT] at hder
  have htargetJet := coordinateMetric_fderiv Q (f • p) (F y₀)
    htarget (R y₀ u) (R y₀ v) (R y₀ w)
  rw [htargetJet]
  change _ =
    (inner ℝ (fderiv ℝ T (F y₀) (R y₀ u) (R y₀ v)) (T (F y₀) (R y₀ w)) +
      inner ℝ (T (F y₀) (R y₀ v)) (fderiv ℝ T (F y₀) (R y₀ u) (R y₀ w))) +
    inner ℝ (T (F y₀) (fderiv ℝ R y₀ u v)) (T (F y₀) (R y₀ w)) +
    inner ℝ (T (F y₀) (R y₀ v)) (T (F y₀) (fderiv ℝ R y₀ u w))
  rw [hder]
  simp only [inner_add_left, inner_add_right]
  abel

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryCoordinateMetricJet
