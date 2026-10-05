import QuaternionicSymmetry.ManifoldQuaternionicFourNativeTwoFormCore
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Bilinear pullback is C∞ jointly in the bilinear form and linear map.
It factors into two actual continuous-linear-map compositions, giving the
polynomial regularity needed for smooth native two-form transitions. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourBilinearPullbackSmooth

open scoped ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def innerPrecomp (T : E →L[ℝ] E) :
    (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E E ℝ).flip T

def bilinearDoublePullback
    (p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E)) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (innerPrecomp p.2).comp (p.1.comp p.2)

theorem bilinearDoublePullback_apply
    (B : E →L[ℝ] E →L[ℝ] ℝ) (T : E →L[ℝ] E) (v w : E) :
    bilinearDoublePullback (B,T) v w = B (T v) (T w) := rfl

theorem bilinearDoublePullback_smooth :
    ContDiff ℝ ∞
      (bilinearDoublePullback (E := E)) := by
  have hinner : ContDiff ℝ ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
        innerPrecomp p.2) :=
    ((ContinuousLinearMap.compL ℝ E E ℝ).flip.contDiff).comp contDiff_snd
  have houter : ContDiff ℝ ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
        p.1.comp p.2) :=
    contDiff_fst.clm_comp contDiff_snd
  exact hinner.clm_comp houter

end
end QuaternionicSymmetry.ManifoldQuaternionicFourBilinearPullbackSmooth
