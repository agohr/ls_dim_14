import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMovingFrame

/-! The moving-frame derivative of the genuine second-affine Möbius
coordinate is the derivative of its independently defined varying-matrix
fraction.  This holds at the south pole as well. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondParameterDerivative

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveMovingFrame
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveSecondMobius
  FourDimensionalHalfSpinProjectiveSecondDerivative

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem second_parameter_fderiv (G : X → Mat2) (x u : X) (w : ℂ)
    (hG : DifferentiableAt ℝ G x) (hden : secondDen (G x) w ≠ 0) :
    fderiv ℝ (fun t => secondMobius (G t) w) x u =
      deriv (secondVaryingMobius (G x) (fderiv ℝ G x u) w) 0 := by
  let S : Mat2 := coordinateSwap
  let G' : X → Mat2 := fun t => S * G t * S
  have hG' : DifferentiableAt ℝ G' x :=
    ((differentiableAt_const S).mul hG).mul_const S
  have hden' : chartDen (G' x) w ≠ 0 := by
    simpa only [G', S, ← secondDen_swap] using hden
  have hC : fderiv ℝ G' x u = S * fderiv ℝ G x u * S := by
    have hd : fderiv ℝ G' x =
        MulOpposite.op S • (S • fderiv ℝ G x) := by
      change fderiv ℝ (fun t => S * G t * S) x = _
      rw [fderiv_mul_const' (hG.const_mul S) S,
        fderiv_const_mul hG S]
    have he := congrArg (fun F : X →L[ℝ] Mat2 => F u) hd
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul,
      op_smul_eq_mul] using he
  have hm : (fun t => secondMobius (G t) w) =
      (fun t => mobius (G' t) w) := by
    funext t
    exact secondMobius_swap (G t) w
  have hv : secondVaryingMobius (G x) (fderiv ℝ G x u) w =
      varyingMobius (G' x) (fderiv ℝ G' x u) w := by
    funext t
    rw [secondVaryingMobius_swap, hC]
  rw [hm, hv]
  exact (mobius_parameter_fderiv G' x hG' u w hden').trans
    (varyingMobius_hasDerivAt (G' x) (fderiv ℝ G' x u) w hden').deriv.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondParameterDerivative
