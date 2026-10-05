import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMovingFrame

/-! The moving-frame derivative of the mixed affine fraction agrees with
its explicit varying-matrix derivative, including zero source coordinate. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedParameterDerivative

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveMovingFrame
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem mixed_parameter_fderiv (G : X → Mat2) (x u : X) (z : ℂ)
    (hG : DifferentiableAt ℝ G x) (hden : mixedDen (G x) z ≠ 0) :
    fderiv ℝ (fun t => mixedMobius (G t) z) x u =
      deriv (mixedVaryingMobius (G x) (fderiv ℝ G x u) z) 0 := by
  let S : Mat2 := coordinateSwap
  let G' : X → Mat2 := fun t => S * G t
  have hG' : DifferentiableAt ℝ G' x :=
    (differentiableAt_const S).mul hG
  have hden' : chartDen (G' x) z ≠ 0 := by
    simpa only [G', S, ← mixedDen_swap] using hden
  have hC : fderiv ℝ G' x u = S * fderiv ℝ G x u := by
    have hd : fderiv ℝ G' x = S • fderiv ℝ G x := by
      change fderiv ℝ (fun t => S * G t) x = _
      rw [fderiv_const_mul hG S]
    have he := congrArg (fun F : X →L[ℝ] Mat2 => F u) hd
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using he
  have hm : (fun t => mixedMobius (G t) z) =
      (fun t => mobius (G' t) z) := by
    funext t
    exact mixedMobius_swap (G t) z
  have hv : mixedVaryingMobius (G x) (fderiv ℝ G x u) z =
      varyingMobius (G' x) (fderiv ℝ G' x u) z := by
    funext t
    rw [mixedVaryingMobius_swap, hC]
  rw [hm, hv]
  exact (mobius_parameter_fderiv G' x hG' u z hden').trans
    (varyingMobius_hasDerivAt (G' x) (fderiv ℝ G' x u) z hden').deriv.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedParameterDerivative
