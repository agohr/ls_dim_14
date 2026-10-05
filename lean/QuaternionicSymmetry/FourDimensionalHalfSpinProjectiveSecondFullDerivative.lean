import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFullTransitionDerivative

/-! The literal base-plus-fiber transition in the second CP¹ affine chart
has the full Fréchet derivative of a conjugated first-chart transition.  In
particular the formula remains valid at its south pole `w = 0`. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondFullDerivative

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveSecondMobius
  FourDimensionalHalfSpinProjectiveTensorOverlap
  FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinProjectiveFullTransitionDerivative

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

def jointSecondTransition (φ : ℍ → ℍ) (G : ℍ → Mat2)
    (t : ℍ × ℂ) : ℍ × ℂ :=
  (φ t.1, secondMobius (G t.1) t.2)

theorem jointSecondTransition_eq (φ : ℍ → ℍ) (G : ℍ → Mat2) :
    jointSecondTransition φ G = jointProjectiveTransition φ
      (fun y => coordinateSwap * G y * coordinateSwap) := by
  funext t
  exact Prod.ext rfl (secondMobius_swap (G t.1) t.2)

theorem second_full_transition_fderiv (φ : ℍ → ℍ) (G : ℍ → Mat2)
    (y : ℍ) (w : ℂ)
    (hφ : DifferentiableAt ℝ φ y)
    (hG : DifferentiableAt ℝ G y)
    (hden : secondDen (G y) w ≠ 0)
    (v : ℍ × ℂ) :
    fderiv ℝ (jointSecondTransition φ G) (y,w) v =
      tangentTransition (fderiv ℝ φ y).toLinearMap
        (fderiv ℝ (fun t => secondMobius (G t) w) y).toLinearMap
        (complexMulReal (deriv (secondMobius (G y)) w)) v := by
  let G' : ℍ → Mat2 := fun t => coordinateSwap * G t * coordinateSwap
  have hG' : DifferentiableAt ℝ G' y :=
    ((differentiableAt_const coordinateSwap).mul hG).mul_const coordinateSwap
  have hden' : chartDen (G' y) w ≠ 0 := by
    simpa only [G', ← secondDen_swap] using hden
  have h := full_transition_fderiv φ G' y w hφ hG' hden' v
  have hmap : jointSecondTransition φ G = jointProjectiveTransition φ G' :=
    jointSecondTransition_eq φ G
  have hfiber : (fun t => secondMobius (G t) w) =
      (fun t => mobius (G' t) w) := by
    funext t
    exact secondMobius_swap (G t) w
  have hscalar : secondMobius (G y) = mobius (G' y) := by
    funext t
    exact secondMobius_swap (G y) t
  simpa only [hmap, hfiber, hscalar] using h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondFullDerivative
