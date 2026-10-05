import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointMobiusDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualTensorOverlap

/-! The block map used in the independent projective almost-complex
overlap theorem is literally the full Fréchet derivative of the actual
base-plus-varying-Möbius affine transition. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFullTransitionDerivative

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveJointMobiusSmooth
  FourDimensionalHalfSpinProjectiveJointMobiusDerivative
  FourDimensionalHalfSpinProjectiveTensorOverlap
  FourDimensionalHalfSpinProjectiveActualTensorOverlap

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

def jointProjectiveTransition (φ : ℍ → ℍ) (G : ℍ → Mat2)
    (t : ℍ × ℂ) : ℍ × ℂ :=
  (φ t.1, mobius (G t.1) t.2)

theorem full_transition_fderiv (φ : ℍ → ℍ) (G : ℍ → Mat2)
    (y : ℍ) (z : ℂ)
    (hφ : DifferentiableAt ℝ φ y)
    (hG : DifferentiableAt ℝ G y)
    (hden : chartDen (G y) z ≠ 0)
    (v : ℍ × ℂ) :
    fderiv ℝ (jointProjectiveTransition φ G) (y,z) v =
      tangentTransition (fderiv ℝ φ y).toLinearMap
        (fderiv ℝ (fun t => mobius (G t) z) y).toLinearMap
        (complexMulReal (deriv (mobius (G y)) z)) v := by
  have hbase : DifferentiableAt ℝ
      (fun t : ℍ × ℂ => φ t.1) (y,z) :=
    hφ.comp (y,z) differentiableAt_fst
  have hfiber := joint_mobius_differentiableAt G y z hG hden
  have hpair := hbase.fderiv_prodMk hfiber
  have hbaseDeriv : fderiv ℝ (fun t : ℍ × ℂ => φ t.1) (y,z) v =
      fderiv ℝ φ y v.1 := by
    have h := (hφ.hasFDerivAt.comp (y,z)
      (hasFDerivAt_fst (𝕜 := ℝ))).fderiv
    have hv := congrArg (fun L : (ℍ × ℂ) →L[ℝ] ℍ => L v) h
    simpa [ContinuousLinearMap.comp_apply] using hv
  have hfiberDeriv := joint_mobius_fderiv G y v.1 z v.2 hG hden
  have hv := congrArg (fun L : (ℍ × ℂ) →L[ℝ] (ℍ × ℂ) => L v) hpair
  apply Prod.ext
  · simpa only [jointProjectiveTransition,
      ContinuousLinearMap.prod_apply, tangentTransition] using
      (congrArg Prod.fst hv).trans hbaseDeriv
  · simpa only [jointProjectiveTransition,
      ContinuousLinearMap.prod_apply, tangentTransition,
      complexMulReal] using (congrArg Prod.snd hv).trans hfiberDeriv

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFullTransitionDerivative
