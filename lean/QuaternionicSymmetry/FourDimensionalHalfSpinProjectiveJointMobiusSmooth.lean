import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointDerivative
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Joint real differentiability of a varying-matrix Möbius map on its
genuine affine denominator-nonzero domain. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointMobiusSmooth

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem joint_mobius_differentiableAt
    (G : X → Mat2) (x : X) (z : ℂ)
    (hG : DifferentiableAt ℝ G x)
    (hden : chartDen (G x) z ≠ 0) :
    DifferentiableAt ℝ
      (fun t : X × ℂ => mobius (G t.1) t.2) (x,z) := by
  have hGprod : DifferentiableAt ℝ
      (fun t : X × ℂ => G t.1) (x,z) :=
    hG.comp (x,z) differentiableAt_fst
  have hnum : DifferentiableAt ℝ
      (fun t : X × ℂ => chartNum (G t.1) t.2) (x,z) := by
    dsimp [chartNum]
    fun_prop
  have hden' : DifferentiableAt ℝ
      (fun t : X × ℂ => chartDen (G t.1) t.2) (x,z) := by
    dsimp [chartDen]
    fun_prop
  have hinv : DifferentiableAt ℝ
      (fun t : X × ℂ => (chartDen (G t.1) t.2)⁻¹) (x,z) :=
    ((hasFDerivAt_inv' (𝕜 := ℝ) hden).comp (x,z)
      hden'.hasFDerivAt).differentiableAt
  simpa only [mobius, div_eq_mul_inv] using hnum.mul hinv

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointMobiusSmooth
