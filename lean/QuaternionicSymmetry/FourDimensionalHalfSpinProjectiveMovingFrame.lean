import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusDerivative
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! A varying complex matrix acts on CP¹ by a Möbius map.  Its real
directional derivative in the parameter equals the varying-frame term in
the already checked projective connection gauge identity. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMovingFrame

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveGaugeAlgebra
  FourDimensionalHalfSpinProjectiveMobiusDerivative

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

private def numLinear (z : ℂ) : Mat2 →ₗ[ℝ] ℂ where
  toFun G := chartNum G z
  map_add' G H := by simp [chartNum, Matrix.add_apply]; ring
  map_smul' c G := by
    simp [chartNum, Matrix.smul_apply, smul_eq_mul]
    ring

private def denLinear (z : ℂ) : Mat2 →ₗ[ℝ] ℂ where
  toFun G := chartDen G z
  map_add' G H := by simp [chartDen, Matrix.add_apply]; ring
  map_smul' c G := by
    simp [chartDen, Matrix.smul_apply, smul_eq_mul]
    ring

private theorem cross_chart (C G : Mat2) (z : ℂ) :
    projectiveCross (C *ᵥ ![1, z]) (G *ᵥ ![1, z]) =
      chartNum C z * chartDen G z - chartDen C z * chartNum G z := by
  simp [projectiveCross, chartNum, chartDen, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]

theorem mobius_parameter_fderiv {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (G : X → Mat2) (x : X) (hG : DifferentiableAt ℝ G x)
    (u : X) (z : ℂ) (hden : chartDen (G x) z ≠ 0) :
    fderiv ℝ (fun y => mobius (G y) z) x u =
      projectiveCross ((fderiv ℝ G x u) *ᵥ ![1, z])
        ((G x) *ᵥ ![1, z]) / (chartDen (G x) z) ^ 2 := by
  let N : Mat2 →L[ℝ] ℂ := (numLinear z).toContinuousLinearMap
  let H : Mat2 →L[ℝ] ℂ := (denLinear z).toContinuousLinearMap
  have hn : HasFDerivAt (fun y => chartNum (G y) z)
      (N.comp (fderiv ℝ G x)) x := by
    exact N.hasFDerivAt.comp x hG.hasFDerivAt
  have hd : HasFDerivAt (fun y => chartDen (G y) z)
      (H.comp (fderiv ℝ G x)) x := by
    exact H.hasFDerivAt.comp x hG.hasFDerivAt
  have hinv := (hasFDerivAt_inv' (𝕜 := ℝ) hden).comp x hd
  have hquot := hn.mul hinv
  have hvalue := congrArg
    (fun T : X →L[ℝ] ℂ => T u) hquot.fderiv
  change fderiv ℝ (fun y => mobius (G y) z) x u = _ at hvalue
  rw [hvalue, cross_chart]
  dsimp [N, H, numLinear, denLinear]
  field_simp [hden]
  ring

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMovingFrame
