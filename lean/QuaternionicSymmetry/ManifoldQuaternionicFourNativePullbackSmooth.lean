import QuaternionicSymmetry.ManifoldQuaternionicFourBilinearAlternation

/-! The actual native alternating-two-form pullback is C∞ jointly in the
form and the frame map. Its proof factors through bounded curried bilinear
forms and the checked antisymmetrization retraction. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativePullbackSmooth

open ManifoldQuaternionicFourBilinearPullbackSmooth
open ManifoldQuaternionicFourNativeBilinearInclusion
open ManifoldQuaternionicFourBilinearAlternation
open scoped ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance

def nativePullbackViaBilinear
    (p : (E [⋀^Fin 2]→L[ℝ] ℝ) × (E →L[ℝ] E)) :
    E [⋀^Fin 2]→L[ℝ] ℝ :=
  bilinearToNativeCLM
    (bilinearDoublePullback (nativeToBilinearCLM p.1,p.2))

theorem nativePullbackViaBilinear_eq
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) (T : E →L[ℝ] E) :
    nativePullbackViaBilinear (α,T) = α.compContinuousLinearMap T := by
  have hB : nativeToBilinearCLM (α.compContinuousLinearMap T) =
      bilinearDoublePullback (nativeToBilinearCLM α,T) := by
    ext v w
    rw [nativeToBilinearCLM_apply, bilinearDoublePullback_apply,
      nativeToBilinearCLM_apply]
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext t
    fin_cases t <;> rfl
  have h := congrArg (bilinearToNativeCLM (E := E)) hB
  rw [bilinearToNativeCLM_nativeToBilinear] at h
  exact h.symm

theorem nativePullback_smooth :
    ContDiff ℝ ∞
      (fun p : (E [⋀^Fin 2]→L[ℝ] ℝ) × (E →L[ℝ] E) =>
        p.1.compContinuousLinearMap p.2) := by
  have hpair : ContDiff ℝ ∞
      (fun p : (E [⋀^Fin 2]→L[ℝ] ℝ) × (E →L[ℝ] E) =>
        (nativeToBilinearCLM p.1,p.2)) :=
    (nativeToBilinearCLM.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hB : ContDiff ℝ ∞
      (fun p : (E [⋀^Fin 2]→L[ℝ] ℝ) × (E →L[ℝ] E) =>
        bilinearDoublePullback (nativeToBilinearCLM p.1,p.2)) :=
    bilinearDoublePullback_smooth.comp hpair
  have hN : ContDiff ℝ ∞ nativePullbackViaBilinear :=
    bilinearToNativeCLM.contDiff.comp hB
  have hfun :
      (fun p : (E [⋀^Fin 2]→L[ℝ] ℝ) × (E →L[ℝ] E) =>
        p.1.compContinuousLinearMap p.2) = nativePullbackViaBilinear := by
    funext p
    exact (nativePullbackViaBilinear_eq p.1 p.2).symm
  rw [hfun]
  exact hN

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativePullbackSmooth
