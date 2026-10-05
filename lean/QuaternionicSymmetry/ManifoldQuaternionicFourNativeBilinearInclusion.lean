import QuaternionicSymmetry.ManifoldQuaternionicFourMultilinearFiniteDimension
import QuaternionicSymmetry.ManifoldQuaternionicFourBilinearPullbackSmooth

/-! Norm-controlled inclusion of native alternating two-forms into curried
bounded bilinear forms. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeBilinearInclusion

open ManifoldQuaternionicFourMultilinearFiniteDimension
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

def nativeToBilinearCLM :
    (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ E
      (E [×1]→L[ℝ] ℝ) (E →L[ℝ] ℝ))
      (continuousMultilinearCurryFin1 ℝ E ℝ).toContinuousLinearMap).comp
    ((continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin 2 => E) ℝ).toContinuousLinearMap.comp
      (ContinuousAlternatingMap.toContinuousMultilinearMapLI
        (𝕜 := ℝ) (ι := Fin 2) (E := E) (F := ℝ)).toContinuousLinearMap)

theorem nativeToBilinearCLM_apply (α : E [⋀^Fin 2]→L[ℝ] ℝ)
    (v w : E) : nativeToBilinearCLM α v w = α ![v,w] := by
  change (continuousMultilinearCurryFin1 ℝ E ℝ)
      ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin 2 => E) ℝ) α.toContinuousMultilinearMap v) w = _
  simp only [continuousMultilinearCurryFin1_apply,
    continuousMultilinearCurryLeftEquiv_apply]
  have hvec : Fin.cons v (Fin.snoc 0 w) = ![v,w] := by
    funext t
    fin_cases t <;> rfl
  rw [hvec]
  rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeBilinearInclusion
