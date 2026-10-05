import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFullTransitionDerivative

/-! The literal second-to-first affine transition has its full Fréchet
derivative, including the moving base-frame term. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseFullDerivative

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveTensorOverlap
  FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinProjectiveFullTransitionDerivative

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

def jointReverseTransition (φ : ℍ → ℍ) (G : ℍ → Mat2)
    (t : ℍ × ℂ) : ℍ × ℂ :=
  (φ t.1, reverseMobius (G t.1) t.2)

theorem jointReverseTransition_eq (φ : ℍ → ℍ) (G : ℍ → Mat2) :
    jointReverseTransition φ G = jointProjectiveTransition φ
      (fun y => G y * coordinateSwap) := by
  funext t
  exact Prod.ext rfl (reverseMobius_swap (G t.1) t.2)

theorem reverse_full_transition_fderiv (φ : ℍ → ℍ) (G : ℍ → Mat2)
    (y : ℍ) (w : ℂ)
    (hφ : DifferentiableAt ℝ φ y)
    (hG : DifferentiableAt ℝ G y)
    (hden : reverseDen (G y) w ≠ 0)
    (v : ℍ × ℂ) :
    fderiv ℝ (jointReverseTransition φ G) (y,w) v =
      tangentTransition (fderiv ℝ φ y).toLinearMap
        (fderiv ℝ (fun t => reverseMobius (G t) w) y).toLinearMap
        (complexMulReal (deriv (reverseMobius (G y)) w)) v := by
  let G' : ℍ → Mat2 := fun t => G t * coordinateSwap
  have hG' : DifferentiableAt ℝ G' y := hG.mul_const coordinateSwap
  have hden' : chartDen (G' y) w ≠ 0 := by
    simpa only [G', ← reverseDen_swap] using hden
  have h := full_transition_fderiv φ G' y w hφ hG' hden' v
  have hmap : jointReverseTransition φ G = jointProjectiveTransition φ G' :=
    jointReverseTransition_eq φ G
  have hfiber : (fun t => reverseMobius (G t) w) =
      (fun t => mobius (G' t) w) := by
    funext t
    exact reverseMobius_swap (G t) w
  have hscalar : reverseMobius (G y) = mobius (G' y) := by
    funext t
    exact reverseMobius_swap (G y) t
  simpa only [hmap, hfiber, hscalar] using h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseFullDerivative
