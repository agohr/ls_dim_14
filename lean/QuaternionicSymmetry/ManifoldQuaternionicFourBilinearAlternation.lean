import QuaternionicSymmetry.ManifoldQuaternionicFourNativeBilinearInclusion
import QuaternionicSymmetry.ContinuousAlternation

/-! Bounded antisymmetrization from curried bilinear maps back to native
alternating two-forms. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourBilinearAlternation

open ManifoldQuaternionicFourMultilinearFiniteDimension
open ManifoldQuaternionicFourNativeBilinearInclusion
open ContinuousAlternation
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
local instance : FiniteDimensional ℝ (E [×1]→L[ℝ] ℝ) :=
  continuousMultilinear_finiteDimensional
local instance : FiniteDimensional ℝ (E [×2]→L[ℝ] ℝ) :=
  continuousMultilinear_finiteDimensional

def bilinearToMultilinearCLM :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E [×2]→L[ℝ] ℝ) :=
  (continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL ℝ E
      (E →L[ℝ] ℝ) (E [×1]→L[ℝ] ℝ))
      (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap)

theorem bilinearToMultilinearCLM_apply
    (B : E →L[ℝ] E →L[ℝ] ℝ) (v : Fin 2 → E) :
    bilinearToMultilinearCLM B v = B (v 0) (v 1) := by
  change (continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin 2 => E) ℝ).symm
      ((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap.comp B) v = _
  simp only [continuousMultilinearCurryLeftEquiv_symm_apply,
    continuousMultilinearCurryFin1_symm_apply]
  rfl

def bilinearToNativeCLM :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 2]→L[ℝ] ℝ) :=
  (1 / 2 : ℝ) •
    ((alternationCLM (ι := Fin 2) (E := E) (F := ℝ)).comp
      bilinearToMultilinearCLM)

theorem bilinearToNativeCLM_nativeToBilinear
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) :
    bilinearToNativeCLM (nativeToBilinearCLM α) = α := by
  have hm : bilinearToMultilinearCLM (nativeToBilinearCLM α) =
      α.toContinuousMultilinearMap := by
    ext v
    rw [bilinearToMultilinearCLM_apply,
      nativeToBilinearCLM_apply]
    have hvec : ![v 0, v 1] = v := by
      funext t
      fin_cases t <;> rfl
    rw [hvec]
    rfl
  simp only [bilinearToNativeCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, hm, alternation_of_alternating]
  change (1 / 2 : ℝ) • (2 : ℕ) • α = α
  rw [← Nat.cast_smul_eq_nsmul ℝ 2 α, smul_smul]
  norm_num

end
end QuaternionicSymmetry.ManifoldQuaternionicFourBilinearAlternation
