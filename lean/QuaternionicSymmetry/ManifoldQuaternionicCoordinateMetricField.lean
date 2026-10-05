import QuaternionicSymmetry.ManifoldQuaternionicCoordinateMetricity
import QuaternionicSymmetry.ManifoldQuaternionicCoordinateSecondBianchi

/-! Smooth coordinate metric as an operator-valued field, for covariant
curvature derivatives. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicCoordinateConnection
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def coordinateMetricField (p : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  Q.chartMetricForm (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem frame_mem (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    (extChartAt 𝓘(ℝ,E) p).symm y ∈
      (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E p) := by
  simpa only [tangentBundleCore_baseSet, coe_achart,
    ← extChartAt_source 𝓘(ℝ,E)] using
    (extChartAt 𝓘(ℝ,E) p).map_target hy

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateMetricField_apply (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    coordinateMetricField Q p y v w = coordinateMetric Q p y v w := by
  rw [coordinateMetricField, Q.chartMetricForm_apply,
    coordinateMetric, solder_eq_toFrame Q p y hy]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateMetricField_differentiableAt (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    DifferentiableAt ℝ (coordinateMetricField Q p) y := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hframe : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) 1
      (Q.chartMetricForm (achart E p)) x :=
    ((Q.smooth_chartMetricForm (achart E p) x (frame_mem p y hy)).of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).contMDiffAt
        (((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet _).mem_nhds
          (frame_mem p y hy))
  have hsymm : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) 1
      (extChartAt 𝓘(ℝ,E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := 1) p y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  exact ((hframe.comp y hsymm).contDiffAt).differentiableAt (by norm_num)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateMetricField_fderiv (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w : E) :
    fderiv ℝ (coordinateMetricField Q p) y u v w =
      coordinateMetric Q p y (coordinateConnection Q D p y u v) w +
        coordinateMetric Q p y v (coordinateConnection Q D p y u w) := by
  have hg := coordinateMetricField_differentiableAt Q p y hy
  have heq : (fun z => coordinateMetricField Q p z v w) =ᶠ[𝓝 y]
      fun z => coordinateMetric Q p z v w := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact coordinateMetricField_apply Q p z hz v w
  have hf := heq.fderiv_eq (𝕜 := ℝ)
  have hfA := congrArg (fun L : E →L[ℝ] ℝ => L u) hf
  change fderiv ℝ (fun z => coordinateMetricField Q p z v w) y u =
    fderiv ℝ (fun z => coordinateMetric Q p z v w) y u at hfA
  rw [LocalConnectionBianchi.fderiv_eval_const
    (hg.clm_apply (differentiableAt_const _)) w u,
    LocalConnectionBianchi.fderiv_eval_const hg v u] at hfA
  exact hfA.trans (coordinateConnection_metric Q D p y hy u v w)

end
end QuaternionicSymmetry.ManifoldQuaternionicCoordinateMetricField
