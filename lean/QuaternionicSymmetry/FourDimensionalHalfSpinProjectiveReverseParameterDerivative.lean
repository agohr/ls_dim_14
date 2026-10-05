import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMovingFrame

/-! The moving-frame derivative of the reverse mixed affine fraction
is the derivative of its explicit varying-matrix expression. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseParameterDerivative

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveMovingFrame
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem reverse_parameter_fderiv (G : X → Mat2) (x u : X) (w : ℂ)
    (hG : DifferentiableAt ℝ G x) (hden : reverseDen (G x) w ≠ 0) :
    fderiv ℝ (fun t => reverseMobius (G t) w) x u =
      deriv (reverseVaryingMobius (G x) (fderiv ℝ G x u) w) 0 := by
  let S : Mat2 := coordinateSwap
  let G' : X → Mat2 := fun t => G t * S
  have hG' : DifferentiableAt ℝ G' x := hG.mul_const S
  have hden' : chartDen (G' x) w ≠ 0 := by
    simpa only [G', S, ← reverseDen_swap] using hden
  have hC : fderiv ℝ G' x u = fderiv ℝ G x u * S := by
    have hd : fderiv ℝ G' x = MulOpposite.op S • fderiv ℝ G x := by
      change fderiv ℝ (fun t => G t * S) x = _
      rw [fderiv_mul_const' hG S]
    have he := congrArg (fun F : X →L[ℝ] Mat2 => F u) hd
    simpa only [ContinuousLinearMap.smul_apply,
      op_smul_eq_mul] using he
  have hm : (fun t => reverseMobius (G t) w) =
      (fun t => mobius (G' t) w) := by
    funext t
    exact reverseMobius_swap (G t) w
  have hv : reverseVaryingMobius (G x) (fderiv ℝ G x u) w =
      varyingMobius (G' x) (fderiv ℝ G' x u) w := by
    funext t
    rw [reverseVaryingMobius_swap, hC]
  rw [hm, hv]
  exact (mobius_parameter_fderiv G' x hG' u w hden').trans
    (varyingMobius_hasDerivAt (G' x) (fderiv ℝ G' x u) w hden').deriv.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseParameterDerivative
