import QuaternionicSymmetry.HomeomorphLieAtlasTransfer

/-! Pullback-atlas smoothness with an arbitrary pre-existing real model with
corners, including a product model. -/

namespace QuaternionicSymmetry.HomeomorphPulledAtlasGeneralRealSmooth
open scoped Manifold ContDiff
noncomputable section

variable {V F H X Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]

theorem smooth_to_old (J : ModelWithCorners ℝ F H) (e : X ≃ₜ Y)
    (newChartsY : ChartedSpace V Y)
    (oldChartsX : ChartedSpace H X)
    (oldChartsY : ChartedSpace H Y)
    (hManifold : letI := newChartsY
      IsManifold 𝓘(ℝ,V) ∞ Y)
    (hCompatible : letI := newChartsY
      letI := oldChartsY
      ContMDiff 𝓘(ℝ,V) J ∞ (id : Y → Y))
    (hInv : letI := oldChartsY
      letI := oldChartsX
      ContMDiff J J ∞ e.symm) :
    letI := newChartsY
    letI := oldChartsY
    letI := oldChartsX
    letI := HomeomorphLieAtlasTransfer.charts (V := V) e
    ContMDiff 𝓘(ℝ,V) J ∞ (id : X → X) := by
  letI := newChartsY
  letI := oldChartsY
  letI := oldChartsX
  letI := HomeomorphLieAtlasTransfer.charts (V := V) e
  letI := hManifold
  have hPull := HomeomorphLieAtlasTransfer.smooth_toFun (V := V) e
  have h := hInv.comp (hCompatible.comp hPull)
  simpa only [Function.comp_def, id_eq, Homeomorph.symm_apply_apply] using h

theorem smooth_from_old (J : ModelWithCorners ℝ F H) (e : X ≃ₜ Y)
    (newChartsY : ChartedSpace V Y)
    (oldChartsX : ChartedSpace H X)
    (oldChartsY : ChartedSpace H Y)
    (hManifold : letI := newChartsY
      IsManifold 𝓘(ℝ,V) ∞ Y)
    (hCompatible : letI := oldChartsY
      letI := newChartsY
      ContMDiff J 𝓘(ℝ,V) ∞ (id : Y → Y))
    (hForward : letI := oldChartsX
      letI := oldChartsY
      ContMDiff J J ∞ e) :
    letI := newChartsY
    letI := oldChartsY
    letI := oldChartsX
    letI := HomeomorphLieAtlasTransfer.charts (V := V) e
    ContMDiff J 𝓘(ℝ,V) ∞ (id : X → X) := by
  letI := newChartsY
  letI := oldChartsY
  letI := oldChartsX
  letI := HomeomorphLieAtlasTransfer.charts (V := V) e
  letI := hManifold
  have hPullInv := HomeomorphLieAtlasTransfer.smooth_invFun (V := V) e
  have h := hPullInv.comp (hCompatible.comp hForward)
  simpa only [Function.comp_def, id_eq, Homeomorph.symm_apply_apply] using h

end
end QuaternionicSymmetry.HomeomorphPulledAtlasGeneralRealSmooth
