import QuaternionicSymmetry.HomeomorphPulledAtlasRealSmooth

/-! The reverse real-smoothness bridge for a genuinely pulled atlas. -/

namespace QuaternionicSymmetry.HomeomorphPulledAtlasRealSmoothInverse
open scoped Manifold ContDiff
noncomputable section

variable {V W X Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace X] [TopologicalSpace Y]

theorem smooth_from_old (e : X ≃ₜ Y)
    (complexCharts : ChartedSpace V Y)
    (realChartsX : ChartedSpace W X)
    (realChartsY : ChartedSpace W Y)
    (hManifold : letI := complexCharts
      IsManifold 𝓘(ℝ,V) ∞ Y)
    (hCompatible : letI := realChartsY
      letI := complexCharts
      ContMDiff 𝓘(ℝ,W) 𝓘(ℝ,V) ∞ (id : Y → Y))
    (hForward : letI := realChartsX
      letI := realChartsY
      ContMDiff 𝓘(ℝ,W) 𝓘(ℝ,W) ∞ e) :
    letI := complexCharts
    letI := realChartsY
    letI := realChartsX
    letI := HomeomorphLieAtlasTransfer.charts (V := V) e
    ContMDiff 𝓘(ℝ,W) 𝓘(ℝ,V) ∞ (id : X → X) := by
  letI := complexCharts
  letI := realChartsY
  letI := realChartsX
  letI := HomeomorphLieAtlasTransfer.charts (V := V) e
  letI := hManifold
  have hPullInv := HomeomorphLieAtlasTransfer.smooth_invFun (V := V) e
  have h := hPullInv.comp (hCompatible.comp hForward)
  simpa only [Function.comp_def, id_eq, Homeomorph.symm_apply_apply] using h

end
end QuaternionicSymmetry.HomeomorphPulledAtlasRealSmoothInverse
