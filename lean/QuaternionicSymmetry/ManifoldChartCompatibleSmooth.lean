import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! A source-free smoothness criterion for a homeomorphism that literally
intertwines the preferred charts on their source sets. -/

namespace QuaternionicSymmetry.ManifoldChartCompatibleSmooth

open scoped Manifold ContDiff

noncomputable section

variable {𝕜 E H X Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]
  (I : ModelWithCorners 𝕜 E H)
  [ChartedSpace H X] [ChartedSpace H Y]
  [IsManifold I ∞ X] [IsManifold I ∞ Y]

theorem homeomorph_contMDiff_of_chart_compatible (f : X ≃ₜ Y)
    (hchart : ∀ x : X, ∀ z : X, z ∈ (chartAt H x).source →
      (chartAt H (f x)) (f z) = (chartAt H x) z) :
    ContMDiff I I ∞ f := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨f.continuous.continuousAt, ?_⟩
  have hid : ContDiffWithinAt 𝕜 ∞ (fun v : E => v) (Set.range I)
      ((extChartAt I x) x) := contDiffWithinAt_id
  apply hid.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with v hv
    let z := (extChartAt I x).symm v
    have hz : z ∈ (chartAt H x).source := by
      simpa only [z, extChartAt_source] using (extChartAt I x).map_target hv
    have h := hchart x z hz
    change (extChartAt I (f x)) (f z) = v
    calc
      (extChartAt I (f x)) (f z) = I ((chartAt H (f x)) (f z)) := rfl
      _ = I ((chartAt H x) z) := congrArg I h
      _ = (extChartAt I x) z := rfl
      _ = v := (extChartAt I x).right_inv hv
  · simpa only [mfld_simps] using congrArg I (hchart x x (mem_chart_source H x))

end
end QuaternionicSymmetry.ManifoldChartCompatibleSmooth
