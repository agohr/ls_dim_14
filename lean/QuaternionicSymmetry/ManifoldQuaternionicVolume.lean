import QuaternionicSymmetry.QuaternionicContinuousVolume
import QuaternionicSymmetry.ManifoldFormPowers
import QuaternionicSymmetry.ManifoldQuaternionicFourFormGluing

/-! The genuine quaternionic four-form has a smooth, nowhere-zero top wedge.
This constructs the volume-form prerequisite without assuming orientation or
nonvanishing. Integration is a separate construction. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicVolume

open Module ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldFormPowers
  ManifoldQuaternionicMetric ManifoldQuaternionicFourForm
  ManifoldQuaternionicFourFormTransitions ManifoldQuaternionicFourFormGluing
  QuaternionicContinuousFundamental QuaternionicContinuousVolume
  ExteriorContinuousPowers ContinuousWedgeUnit ContinuousWedge
open scoped Manifold ContDiff Topology

noncomputable section
set_option maxHeartbeats 800000
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem chartFour_eq_fundamental (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    chartFour Q i x = (fundamental (Q.reduction.Q i)).compContinuousLinearMap
      (Q.frames.toFrame i x) := by
  unfold chartFour fundamental
  simp_rw [chartKahler_eq_frameKahler Q i x hi]
  ext v
  simp only [ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply Finset.sum_congr rfl
  intro t ht
  exact congrArg (fun a : E [⋀^Fin 4]→L[ℝ] ℝ => a v)
    (ExteriorContinuousPowers.wedge_comp (Q.frames.toFrame i x)
      (kahler (Q.reduction.Q i) t) (kahler (Q.reduction.Q i) t)).symm

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem frame_dimension (i : atlas E M) :
    (Q.reduction.Q i).quaternionicDimension = Module.finrank ℝ E / 4 := by
  have h := (Q.reduction.Q i).real_finrank
  omega

omit [Nontrivial E] in
theorem chartFour_topPower_ne_zero (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    wedgePower (chartFour Q i x) (Module.finrank ℝ E / 4) ≠ 0 := by
  rw [chartFour_eq_fundamental Q i x hi, ← wedgePower_comp]
  intro h
  have hv := wedgePower_fundamental_ne_zero (Q.reduction.Q i)
  rw [frame_dimension Q i] at hv
  apply hv
  ext v
  have he := congrArg (fun a : E [⋀^Fin (4 * (Module.finrank ℝ E / 4))]→L[ℝ] ℝ =>
    a (fun t => Q.frames.fromFrame i x (v t))) h
  simpa [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, Q.frames.to_from i x hi] using he

theorem fundamental_power_chart_ne_zero (p : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inChartModel p (formPower (fundamentalFourForm Q) (Module.finrank ℝ E / 4)) y ≠ 0 := by
  rw [inChartModel_formPower]
  have he := (fourFormData Q).inChartModel_toForm p hy
  change inChartModel p (fundamentalFourForm Q) y = _ at he
  rw [he]
  apply chartFour_topPower_ne_zero
  change (extChartAt 𝓘(ℝ, E) p).symm y ∈
    (tangentBundleCore 𝓘(ℝ, E) M).baseSet (achart E p)
  simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using
    (extChartAt 𝓘(ℝ, E) p).map_target hy

variable [Nonempty M]

include Q in
omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem model_dimension : 4 * (Module.finrank ℝ E / 4) = Module.finrank ℝ E := by
  let x : M := Classical.choice inferInstance
  have h := (Q.reduction.Q (achart E x)).real_finrank
  rw [frame_dimension Q] at h
  exact h.symm

/-- A smooth genuine tangent top-form constructed from the global quaternionic
four-form. Its normalization here is the unscaled top wedge. -/
def fundamentalTopForm : Form 𝓘(ℝ, E) M (Module.finrank ℝ E) :=
  castForm (model_dimension Q)
    (formPower (fundamentalFourForm Q) (Module.finrank ℝ E / 4))

theorem fundamentalTopForm_smooth : ChartSmooth (fundamentalTopForm Q) :=
  chartSmooth_castForm _ _
    (formPower_smooth _ (fundamentalFourForm_smooth Q) _)

theorem fundamentalTopForm_chart_ne_zero (p : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inChartModel p (fundamentalTopForm Q) y ≠ 0 := by
  rw [fundamentalTopForm, inChartModel_castForm]
  have hinj {a b : ℕ} (h : a = b) :
      Function.Injective (castAlternating (E := E) h) := by cases h; exact fun _ _ h => h
  intro hz
  apply fundamental_power_chart_ne_zero Q p hy
  apply hinj (model_dimension Q)
  have hzero {a b : ℕ} (h : a = b) :
      castAlternating (E := E) h 0 = 0 := by cases h; rfl
  exact hz.trans (hzero (model_dimension Q)).symm

/-- Nonvanishing on each actual tangent fiber. -/
theorem fundamentalTopForm_ne_zero (x : M) : fundamentalTopForm Q x ≠ 0 := by
  intro hz
  apply fundamentalTopForm_chart_ne_zero Q x (mem_extChartAt_target x)
  ext v
  rw [inChartModel_self_apply,
    (extChartAt 𝓘(ℝ, E) x).left_inv (mem_extChartAt_source x), hz]
  rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicVolume
