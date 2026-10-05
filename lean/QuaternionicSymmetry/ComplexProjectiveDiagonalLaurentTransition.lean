import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapFractions
import QuaternionicSymmetry.ComplexProjectiveDiagonalAlgebraicCharts

/-! The regular Laurent coefficient ratios satisfy the same cocycle law
as actual projective coordinate fractions on a pairwise overlap. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalLaurentTransition

open ComplexProjectiveDiagonalAlgebraicCharts
noncomputable section

variable {r d : ℕ}

theorem laurentRatio_cocycle
    (μ : Fin (d + 1) → Fin r → ℤ)
    (i j k : Fin (d + 1)) :
    laurentMonomial (μ k - μ i) * laurentMonomial (μ i - μ j) =
      laurentMonomial (μ k - μ j) := by
  have h : (μ k - μ i) + (μ i - μ j) = μ k - μ j := by abel
  simp only [laurentMonomial, AddMonoidAlgebra.single_mul_single, one_mul, h]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalLaurentTransition
