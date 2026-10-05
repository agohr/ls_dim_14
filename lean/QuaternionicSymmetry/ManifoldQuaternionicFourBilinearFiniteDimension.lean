import QuaternionicSymmetry.ManifoldQuaternionicFourBilinearPullbackSmooth
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace QuaternionicSymmetry.ManifoldQuaternionicFourBilinearFiniteDimension

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

theorem bilinear_finiteDimensional :
    FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

end
end QuaternionicSymmetry.ManifoldQuaternionicFourBilinearFiniteDimension
