import QuaternionicSymmetry.HomeomorphLieAtlasTransfer

/-! A generic smooth-composition bridge for an atlas pulled across a
homeomorphism. The old real atlases on source and target remain independent. -/

namespace QuaternionicSymmetry.HomeomorphPulledAtlasRealSmooth
open scoped Manifold ContDiff
noncomputable section

variable {V W X Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace X] [TopologicalSpace Y]

theorem smooth_to_old (e : X ≃ₜ Y)
    (complexCharts : ChartedSpace V Y)
    (realChartsX : ChartedSpace W X)
    (realChartsY : ChartedSpace W Y)
    (hManifold : letI := complexCharts
      IsManifold 𝓘(ℝ,V) ∞ Y)
    (hCompatible : letI := complexCharts
      letI := realChartsY
      ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,W) ∞ (id : Y → Y))
    (hInv : letI := realChartsY
      letI := realChartsX
      ContMDiff 𝓘(ℝ,W) 𝓘(ℝ,W) ∞ e.symm) :
    letI := complexCharts
    letI := realChartsY
    letI := realChartsX
    letI := HomeomorphLieAtlasTransfer.charts (V := V) e
    ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,W) ∞ (id : X → X) := by
  letI := complexCharts
  letI := realChartsY
  letI := realChartsX
  letI := HomeomorphLieAtlasTransfer.charts (V := V) e
  letI := hManifold
  have hPull := HomeomorphLieAtlasTransfer.smooth_toFun (V := V) e
  have h := hInv.comp (hCompatible.comp hPull)
  simpa only [Function.comp_def, id_eq, Homeomorph.symm_apply_apply] using h

end
end QuaternionicSymmetry.HomeomorphPulledAtlasRealSmooth
