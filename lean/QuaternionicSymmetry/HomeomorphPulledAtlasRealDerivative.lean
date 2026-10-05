import QuaternionicSymmetry.HomeomorphPulledAtlasDerivative
import QuaternionicSymmetry.HomeomorphPulledAtlasGeneralRealSmooth

/-! Chain-rule comparison of the real derivatives of identity maps out of a
pulled complex atlas and the original atlas. -/

namespace QuaternionicSymmetry.HomeomorphPulledAtlasRealDerivative
open scoped Manifold ContDiff
noncomputable section

variable {V F H X Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]

theorem derivative_to_old_eq (J : ModelWithCorners ℝ F H) (e : X ≃ₜ Y)
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
    (x : X) :
    letI := newChartsY
    letI := oldChartsY
    letI := oldChartsX
    letI := HomeomorphLieAtlasTransfer.charts (V := V) e
    mfderiv 𝓘(ℝ,V) J (id : X → X) x =
      mfderiv 𝓘(ℝ,V) J (id : Y → Y) (e x) := by
  letI := newChartsY
  letI := oldChartsY
  letI := oldChartsX
  letI := HomeomorphLieAtlasTransfer.charts (V := V) e
  letI := hManifold
  have hPull := HomeomorphLieAtlasTransfer.smooth_toFun (V := V) e
  have hMiddle := hCompatible.comp hPull
  have hChain1 := mfderiv_comp (f := (id : Y → Y) ∘ e)
    (g := e.symm) (x := x)
    (hInv.mdifferentiableAt (by simp)) (hMiddle.mdifferentiableAt (by simp))
  have hChain2 := mfderiv_comp (f := e) (g := (id : Y → Y)) (x := x)
    (hCompatible.mdifferentiableAt (by simp)) (hPull.mdifferentiableAt (by simp))
  calc
    mfderiv 𝓘(ℝ,V) J (id : X → X) x =
        mfderiv 𝓘(ℝ,V) J (e.symm ∘ ((id : Y → Y) ∘ e)) x := by
          congr 1
          funext y
          exact (e.symm_apply_apply y).symm
    _ = (mfderiv J J e.symm (e x)).comp
          (mfderiv 𝓘(ℝ,V) J ((id : Y → Y) ∘ e) x) := hChain1
    _ = mfderiv 𝓘(ℝ,V) J (id : Y → Y) (e x) := by
      rw [hChain2, hOldDerivative x,
        HomeomorphPulledAtlasDerivative.mfderiv_toFun_eq_id e x]
      apply ContinuousLinearMap.ext
      intro v
      rfl

end
end QuaternionicSymmetry.HomeomorphPulledAtlasRealDerivative
