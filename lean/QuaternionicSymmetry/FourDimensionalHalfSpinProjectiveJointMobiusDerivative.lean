import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointMobiusSmooth
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusRealTangent

/-! The literal full real derivative of the varying CP¹ Möbius map equals
the sum of its independently checked moving-frame and holomorphic fiber
terms. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointMobiusDerivative

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveJointDerivative
  FourDimensionalHalfSpinProjectiveJointMobiusSmooth
  FourDimensionalHalfSpinProjectiveMobiusRealTangent

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem joint_mobius_fderiv (G : X → Mat2) (x u : X) (z v : ℂ)
    (hG : DifferentiableAt ℝ G x)
    (hden : chartDen (G x) z ≠ 0) :
    fderiv ℝ (fun t : X × ℂ => mobius (G t.1) t.2)
      (x,z) (u,v) =
      fderiv ℝ (fun a => mobius (G a) z) x u +
        deriv (mobius (G x)) z * v := by
  rw [fderiv_joint_split _ x z
    (joint_mobius_differentiableAt G x z hG hden) u v]
  rw [mobius_real_fderiv (G x) z v hden]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointMobiusDerivative
