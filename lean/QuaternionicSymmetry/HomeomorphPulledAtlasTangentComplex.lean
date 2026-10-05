import QuaternionicSymmetry.HomeomorphPulledAtlasRealDerivative
import Mathlib.Analysis.Complex.Basic

/-! Generic transport of the exact real tangent complex-structure law across
a pulled complex atlas, when the old real derivative and tensor agree. -/

namespace QuaternionicSymmetry.HomeomorphPulledAtlasTangentComplex
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
    (JX : X → F →L[ℝ] F) (JY : Y → F →L[ℝ] F)
    (hJ : ∀ (x : X) (u : F), JX x u = JY (e x) u)
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
  exact (hY (e x) v).trans (hJ x _).symm

end
end QuaternionicSymmetry.HomeomorphPulledAtlasTangentComplex
