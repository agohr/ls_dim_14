import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFullTransitionDerivative

/-! The literal first-to-second affine transition has its full Fréchet
derivative, including the moving base-frame term. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedFullDerivative

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveTensorOverlap
  FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinProjectiveFullTransitionDerivative

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

def jointMixedTransition (φ : ℍ → ℍ) (G : ℍ → Mat2)
    (t : ℍ × ℂ) : ℍ × ℂ :=
  (φ t.1, mixedMobius (G t.1) t.2)

theorem jointMixedTransition_eq (φ : ℍ → ℍ) (G : ℍ → Mat2) :
    jointMixedTransition φ G = jointProjectiveTransition φ
      (fun y => coordinateSwap * G y) := by
  funext t
  exact Prod.ext rfl (mixedMobius_swap (G t.1) t.2)

theorem mixed_full_transition_fderiv (φ : ℍ → ℍ) (G : ℍ → Mat2)
    (y : ℍ) (z : ℂ)
    (hφ : DifferentiableAt ℝ φ y)
    (hG : DifferentiableAt ℝ G y)
    (hden : mixedDen (G y) z ≠ 0)
    (v : ℍ × ℂ) :
    fderiv ℝ (jointMixedTransition φ G) (y,z) v =
      tangentTransition (fderiv ℝ φ y).toLinearMap
        (fderiv ℝ (fun t => mixedMobius (G t) z) y).toLinearMap
        (complexMulReal (deriv (mixedMobius (G y)) z)) v := by
  let G' : ℍ → Mat2 := fun t => coordinateSwap * G t
  have hG' : DifferentiableAt ℝ G' y :=
    (differentiableAt_const coordinateSwap).mul hG
  have hden' : chartDen (G' y) z ≠ 0 := by
    simpa only [G', ← mixedDen_swap] using hden
  have h := full_transition_fderiv φ G' y z hφ hG' hden' v
  have hmap : jointMixedTransition φ G = jointProjectiveTransition φ G' :=
    jointMixedTransition_eq φ G
  have hfiber : (fun t => mixedMobius (G t) z) =
      (fun t => mobius (G' t) z) := by
    funext t
    exact mixedMobius_swap (G t) z
  have hscalar : mixedMobius (G y) = mobius (G' y) := by
    funext t
    exact mixedMobius_swap (G y) t
  simpa only [hmap, hfiber, hscalar] using h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedFullDerivative
