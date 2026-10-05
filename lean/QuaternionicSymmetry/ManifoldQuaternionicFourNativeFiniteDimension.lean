import QuaternionicSymmetry.ManifoldQuaternionicFourNativePullbackSmooth
import QuaternionicSymmetry.ManifoldQuaternionicFourBilinearFiniteDimension

/-! The native alternating two-form space is genuinely finite-dimensional,
via its proved bounded injection into the finite-dimensional bilinear forms. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeFiniteDimension

open ManifoldQuaternionicFourNativeBilinearInclusion
open ManifoldQuaternionicFourBilinearAlternation
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

theorem native_finiteDimensional :
    FiniteDimensional ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := by
  letI : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    ManifoldQuaternionicFourBilinearFiniteDimension.bilinear_finiteDimensional
  apply FiniteDimensional.of_injective
    (nativeToBilinearCLM (E := E)).toLinearMap
  intro α β h
  calc
    α = bilinearToNativeCLM (nativeToBilinearCLM α) :=
      (bilinearToNativeCLM_nativeToBilinear α).symm
    _ = bilinearToNativeCLM (nativeToBilinearCLM β) :=
      congrArg (bilinearToNativeCLM (E := E)) h
    _ = β := bilinearToNativeCLM_nativeToBilinear β

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeFiniteDimension
