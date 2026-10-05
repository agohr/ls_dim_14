import QuaternionicSymmetry.HomeomorphPulledAtlasRealDerivative
import Mathlib.Analysis.Complex.Basic

/-! Tensor transport for a real-linear almost-complex endomorphism. No
global continuity of the endomorphism is needed for this pointwise law. -/

namespace QuaternionicSymmetry.HomeomorphPulledAtlasTangentLinear
open scoped Manifold ContDiff
noncomputable section

variable {V F H X Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]

theorem tangentI_pullback (J : ModelWithCorners ℝ F H) (e : X ≃ₜ Y)
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
      ContMDiff J J ∞ e.symm)
    (hOldDerivative : letI := oldChartsY
      letI := oldChartsX
      ∀ x : X, mfderiv J J e.symm (e x) = ContinuousLinearMap.id ℝ F)
    (JX : X → F →ₗ[ℝ] F) (JY : Y → F →ₗ[ℝ] F)
    (hJ : ∀ (y : Y) (u : F), JY y u = JX (e.symm y) u)
    (hY : letI := newChartsY
      letI := oldChartsY
      ∀ (y : Y) (v : V),
        mfderiv 𝓘(ℝ,V) J (id : Y → Y) y ((Complex.I : ℂ) • v) =
          JY y (mfderiv 𝓘(ℝ,V) J (id : Y → Y) y v))
    (x : X) (v : V) :
    letI := newChartsY
    letI := oldChartsY
    letI := oldChartsX
    letI := HomeomorphLieAtlasTransfer.charts (V := V) e
    mfderiv 𝓘(ℝ,V) J (id : X → X) x ((Complex.I : ℂ) • v) =
      JX x (mfderiv 𝓘(ℝ,V) J (id : X → X) x v) := by
  letI := newChartsY
  letI := oldChartsY
  letI := oldChartsX
  letI := HomeomorphLieAtlasTransfer.charts (V := V) e
  have hD := HomeomorphPulledAtlasRealDerivative.derivative_to_old_eq
    J e newChartsY oldChartsX oldChartsY hManifold hCompatible hInv hOldDerivative x
  rw [hD]
  calc
    _ = JY (e x) (mfderiv 𝓘(ℝ,V) J (id : Y → Y) (e x) v) := hY (e x) v
    _ = JX x (mfderiv 𝓘(ℝ,V) J (id : Y → Y) (e x) v) := by
      simpa only [e.symm_apply_apply] using hJ (e x) _

end
end QuaternionicSymmetry.HomeomorphPulledAtlasTangentLinear
