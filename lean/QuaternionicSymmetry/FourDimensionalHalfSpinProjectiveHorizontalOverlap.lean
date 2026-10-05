import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMovingFrame

/-! The matrix gauge law is exactly the covariance of the local
projective horizontal graph under the actual Möbius tangent transition. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveHorizontalOverlap

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveMovingFrame

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

def projectiveHorizontalVertical (B : Mat2) (z : ℂ) : ℂ :=
  -affineGenerator B z

/-- The full moving-frame horizontal-chain equation: derivative in the
base parameter plus derivative in the fiber coordinate carries the
negative connection generator to the corresponding target generator. -/
theorem horizontal_mobius_covariance {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (G : X → Mat2) (x : X) (hG : DifferentiableAt ℝ G x)
    (u : X) (A B : Mat2) (z : ℂ)
    (hgauge : G x * B = A * G x + fderiv ℝ G x u)
    (hden : chartDen (G x) z ≠ 0) :
    fderiv ℝ (fun y => mobius (G y) z) x u +
      deriv (mobius (G x)) z * projectiveHorizontalVertical B z =
        projectiveHorizontalVertical A (mobius (G x) z) := by
  rw [mobius_parameter_fderiv G x hG u z hden]
  have hchain := affine_gauge_chain (G x) A B (fderiv ℝ G x u)
    z hgauge hden
  rw [(varyingMobius_hasDerivAt (G x) (fderiv ℝ G x u) z hden).deriv]
    at hchain
  dsimp [projectiveHorizontalVertical]
  linear_combination -hchain

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveHorizontalOverlap
