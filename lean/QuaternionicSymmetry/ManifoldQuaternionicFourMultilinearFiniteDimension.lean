import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Continuous multilinear maps on finite-dimensional real spaces form a
finite-dimensional space: include them in the algebraic multilinear maps. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourMultilinearFiniteDimension

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Finite ι]

theorem continuousMultilinear_finiteDimensional :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ) :=
  FiniteDimensional.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear
      (R' := ℝ) (A := ℝ) (M₁ := fun _ : ι => E) (M₂ := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective

end
end QuaternionicSymmetry.ManifoldQuaternionicFourMultilinearFiniteDimension
