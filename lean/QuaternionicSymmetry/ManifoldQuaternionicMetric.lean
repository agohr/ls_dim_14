import QuaternionicSymmetry.ManifoldQuaternionicReduction
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Metric compatibility for an almost-quaternionic tangent reduction. The metric
is constructed from orthonormal adapted frames and shown independent of the
local frame on overlaps. This does not supply a Levi-Civita connection.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicMetric

open Bundle
open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

/-- An almost-quaternionic tangent reduction whose adapted frames are
orthonormal for one metric. On overlaps, transitions may rotate the local
quaternionic triples while preserving their span. -/
structure SmoothQuaternionicHermitianTangent extends
    ManifoldQuaternionicReduction.SmoothAlmostQuaternionicTangent
      (I := I) (M := M) (n := n) where
  transition_inner : ∀ i j : atlas H M, ∀ x,
    x ∈ frames.adaptedCore.baseSet i → x ∈ frames.adaptedCore.baseSet j →
    ∀ v w : E,
      inner ℝ (frames.coordChange i j x v) (frames.coordChange i j x w) = inner ℝ v w

namespace SmoothQuaternionicHermitianTangent

variable (Q : SmoothQuaternionicHermitianTangent (I := I) (M := M) (n := n))

/-- The tangent-fiber metric obtained by returning a vector to the adapted
orthonormal frame at its base point. -/
def tangentMetricForm (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let T := Q.frames.toFrame ((tangentBundleCore I M).indexAt x) x
  ((ContinuousLinearMap.compL ℝ E E ℝ).flip T).comp ((innerSL ℝ).comp T)

theorem tangentMetricForm_apply (x : M) (v w : TangentSpace I x) :
    Q.tangentMetricForm x v w =
      inner ℝ (Q.frames.toFrame ((tangentBundleCore I M).indexAt x) x v)
        (Q.frames.toFrame ((tangentBundleCore I M).indexAt x) x w) := rfl

theorem tangentMetricForm_symm (x : M) (v w : TangentSpace I x) :
    Q.tangentMetricForm x v w = Q.tangentMetricForm x w v := by
  simp only [tangentMetricForm_apply, real_inner_comm]

theorem tangentMetricForm_pos (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < Q.tangentMetricForm x v v := by
  rw [tangentMetricForm_apply]
  apply real_inner_self_pos.mpr
  intro h
  apply hv
  have hh := congrArg
    (Q.frames.fromFrame ((tangentBundleCore I M).indexAt x) x) h
  simpa only [map_zero, Q.frames.from_to _ x
    ((tangentBundleCore I M).mem_baseSet_at x)] using hh

theorem tangentMetric_chart_eq (i : atlas H M) (x : M)
    (hi : x ∈ (tangentBundleCore I M).baseSet i) (v w : TangentSpace I x) :
    Q.tangentMetricForm x v w =
      inner ℝ (Q.frames.toFrame i x
        ((tangentBundleCore I M).coordChange
          ((tangentBundleCore I M).indexAt x) i x v))
        (Q.frames.toFrame i x
          ((tangentBundleCore I M).coordChange
            ((tangentBundleCore I M).indexAt x) i x w)) := by
  let k := (tangentBundleCore I M).indexAt x
  have hk := (tangentBundleCore I M).mem_baseSet_at x
  have hv' : Q.frames.coordChange k i x (Q.frames.toFrame k x v) =
      Q.frames.toFrame i x ((tangentBundleCore I M).coordChange k i x v) := by
    rw [Q.frames.coordChange_apply, Q.frames.from_to k x hk]
  have hw' : Q.frames.coordChange k i x (Q.frames.toFrame k x w) =
      Q.frames.toFrame i x ((tangentBundleCore I M).coordChange k i x w) := by
    rw [Q.frames.coordChange_apply, Q.frames.from_to k x hk]
  rw [Q.tangentMetricForm_apply, ← hv', ← hw']
  exact (Q.transition_inner k i x hk hi _ _).symm

/-- In an adapted tangent chart, the local quaternionic generators preserve
the metric represented by that chart's frame. -/
theorem chartGenerator_isometry (i : atlas H M) (x : M)
    (hi : x ∈ (tangentBundleCore I M).baseSet i)
    (t : Fin 3) (v w : E) :
    inner ℝ (Q.frames.toFrame i x (Q.toSmoothAlmostQuaternionicTangent.chartGenerator i t x v))
      (Q.frames.toFrame i x (Q.toSmoothAlmostQuaternionicTangent.chartGenerator i t x w)) =
        inner ℝ (Q.frames.toFrame i x v) (Q.frames.toFrame i x w) := by
  let S := Q.reduction.Q i
  let T := Q.frames.toFrame i x
  let U := Q.frames.fromFrame i x
  have hTU (a : E) : T (U a) = a := Q.frames.to_from i x hi a
  change inner ℝ (T (U ((VectorBundleFrameTransitions.quaternionicGenerator S t) (T v))))
      (T (U ((VectorBundleFrameTransitions.quaternionicGenerator S t) (T w)))) =
      inner ℝ (T v) (T w)
  rw [hTU, hTU]
  fin_cases t
  · exact S.I.inner_map_map _ _
  · exact S.J.inner_map_map _ _
  · exact S.K.inner_map_map _ _

/-- A change between two adapted tangent frames, as an actual continuous
linear equivalence. Its inverse is obtained from the tangent cocycle. -/
def frameTransition (i j : atlas H M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) : E ≃L[ℝ] E where
  toFun := Q.frames.coordChange i j x
  invFun := Q.frames.coordChange j i x
  map_add' := by intros; simp
  map_smul' := by intros; simp
  left_inv v := by
    calc
      Q.frames.coordChange j i x (Q.frames.coordChange i j x v) =
        Q.frames.coordChange i i x v := Q.frames.coordChange_comp i j i x hi hj hi v
      _ = v := Q.frames.coordChange_self i x hi v
  right_inv v := by
    calc
      Q.frames.coordChange i j x (Q.frames.coordChange j i x v) =
        Q.frames.coordChange j j x v := Q.frames.coordChange_comp j i j x hj hi hj v
      _ = v := Q.frames.coordChange_self j x hj v
  continuous_toFun := (Q.frames.coordChange i j x).continuous
  continuous_invFun := (Q.frames.coordChange j i x).continuous

theorem frameTransition_inner (i j : atlas H M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) (v w : E) :
    inner ℝ (Q.frameTransition i j x hi hj v)
      (Q.frameTransition i j x hi hj w) = inner ℝ v w :=
  Q.transition_inner i j x hi hj v w

theorem frameTransition_comp (i j k : atlas H M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (hk : x ∈ Q.frames.adaptedCore.baseSet k) :
    (Q.frameTransition i j x hi hj).trans (Q.frameTransition j k x hj hk) =
      Q.frameTransition i k x hi hk := by
  ext v
  exact Q.frames.coordChange_comp i j k x hi hj hk v

/-- The actual adapted frame transition preserves the local quaternionic
subspace, so it lies in the quaternionic Hermitian frame groupoid. -/
theorem frameTransition_quaternionicSpan (i j : atlas H M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    Submodule.map
      ((VectorBundleFrameTransitions.transitionAtlas Q.frames.adaptedCore).adjointCoordChange
        i j x).toLinearMap
      (VectorBundleFrameTransitions.quaternionicSpan (Q.reduction.Q i)) =
      VectorBundleFrameTransitions.quaternionicSpan (Q.reduction.Q j) :=
  Q.reduction.map_span_eq i j x hi hj

/-- The bilinear metric written in a single adapted chart. -/
private def realInnerCLM : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (innerₗ E) 1 (fun x y => by
    simpa only [one_mul, innerₗ_apply_apply] using norm_inner_le_norm x y)

def chartMetricForm (i : atlas H M) (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  let T := Q.frames.toFrame i x
  ((ContinuousLinearMap.compL ℝ E E ℝ).flip T).comp (realInnerCLM.comp T)

theorem chartMetricForm_apply (i : atlas H M) (x : M) (v w : E) :
    Q.chartMetricForm i x v w =
      inner ℝ (Q.frames.toFrame i x v) (Q.frames.toFrame i x w) := rfl

theorem smooth_chartMetricForm (i : atlas H M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n (Q.chartMetricForm i)
      ((tangentBundleCore I M).baseSet i) := by
  have hto := Q.frames.smooth_to i
  have hc : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n
      (fun _ : M => realInnerCLM (E := E))
      ((tangentBundleCore I M).baseSet i) := contMDiffOn_const
  have hinner := hc.clm_comp hto
  have hpre := hto.clm_precomp (F₃ := ℝ)
  have hpost := hpre.clm_postcomp (F₁ := E)
  convert hpost.clm_apply hinner using 1

theorem tangentMetric_inCoordinates_eq (x₀ x : M)
    (hx : x ∈ (chartAt H x₀).source) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x
      (Q.tangentMetricForm x) = Q.chartMetricForm (achart H x₀) x := by
  ext v w
  rw [inCoordinates_apply_eq₂]
  · simp only [Trivial.fiberBundle_trivializationAt',
      Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq]
    change Q.tangentMetricForm x
      ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x v)
      ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x w) = _
    rw [TangentBundle.symmL_trivializationAt_eq_core hx]
    rw [Q.tangentMetric_chart_eq (achart H x₀) x (by
      simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using hx)]
    have hi : x ∈ (tangentBundleCore I M).baseSet (achart H x₀) := by
      simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using hx
    have hj := (tangentBundleCore I M).mem_baseSet_at x
    have hcancel (u : E) :
        (tangentBundleCore I M).coordChange
          ((tangentBundleCore I M).indexAt x) (achart H x₀) x
          ((tangentBundleCore I M).coordChange (achart H x₀) (achart H x) x u) = u := by
      calc
        _ = (tangentBundleCore I M).coordChange (achart H x₀) (achart H x₀) x u :=
          (tangentBundleCore I M).coordChange_comp
            (achart H x₀) (achart H x) (achart H x₀) x
              ⟨⟨hi, by simp⟩, hi⟩ u
        _ = u := (tangentBundleCore I M).coordChange_self (achart H x₀) x hi u
    rw [Q.chartMetricForm_apply]
    congr 1
    · exact congrArg (Q.frames.toFrame (achart H x₀) x) (hcancel v)
    · exact congrArg (Q.frames.toFrame (achart H x₀) x) (hcancel w)
  · exact hx
  · exact hx
  · simp

theorem tangentMetric_contMDiff :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (Q.tangentMetricForm x)) := by
  intro x₀
  rw [contMDiffAt_section]
  let s := (chartAt H x₀).source
  have hs : s ∈ 𝓝 x₀ := (chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)
  have hlocal : ∀ x ∈ s,
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀
          ⟨x, Q.tangentMetricForm x⟩).2 = Q.chartMetricForm (achart H x₀) x := by
    intro x hx
    rw [hom_trivializationAt_apply]
    exact Q.tangentMetric_inCoordinates_eq x₀ x hx
  have hi : x₀ ∈ (tangentBundleCore I M).baseSet (achart H x₀) := by
    simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
      mem_chart_source H x₀
  have hs' : (tangentBundleCore I M).baseSet (achart H x₀) ∈ 𝓝 x₀ := by
    simpa only [s, tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using hs
  have hchart := (Q.smooth_chartMetricForm (achart H x₀) x₀ hi).contMDiffAt hs'
  exact hchart.congr_of_eventuallyEq (by
    filter_upwards [hs] with x hx
    exact hlocal x hx)

theorem tangentMetric_isVonNBounded (x : M) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | Q.tangentMetricForm x v v < 1} := by
  let k := (tangentBundleCore I M).indexAt x
  let U := Q.frames.fromFrame k x
  have hsubset : {v : TangentSpace I x | Q.tangentMetricForm x v v < 1} ⊆
      U '' Metric.ball (0 : E) 1 := by
    intro v hv
    refine ⟨Q.frames.toFrame k x v, ?_, ?_⟩
    · have hsq : ‖Q.frames.toFrame k x v‖ ^ 2 < 1 := by
        simpa only [Q.tangentMetricForm_apply, real_inner_self_eq_norm_sq] using hv
      have hn := norm_nonneg (Q.frames.toFrame k x v)
      simp only [Metric.mem_ball, dist_zero_right]
      nlinarith
    · exact Q.frames.from_to k x ((tangentBundleCore I M).mem_baseSet_at x) v
  exact ((NormedSpace.isVonNBounded_ball ℝ E 1).image U).subset hsubset

/-- The smooth Riemannian metric induced by orthonormal adapted tangent frames. -/
def riemannianMetric : Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _) where
  inner := Q.tangentMetricForm
  symm := Q.tangentMetricForm_symm
  pos := Q.tangentMetricForm_pos
  isVonNBounded := Q.tangentMetric_isVonNBounded
  contMDiff := Q.tangentMetric_contMDiff

end SmoothQuaternionicHermitianTangent

end
end QuaternionicSymmetry.ManifoldQuaternionicMetric
