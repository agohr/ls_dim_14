import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNormalizerTransitive
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseMobius

/-! The north differential is now explicitly attached to the true
projectivized half-spin point `[1:z]`, not merely to a free spinor formula. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthDerivative

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveActualBaseMobius
  FourDimensionalHalfSpinHopfNorthDerivative
  FourDimensionalHalfSpinHopfChartFormula
  FourDimensionalHalfSpinHopfProjectiveDescent
  ComplexProjectiveTopology

noncomputable section

theorem projectiveHopf_affine_coordinates (z : ℂ) :
    (projectiveHopf (affineSpinorPoint z)).1 = northCoordinates z := by
  rw [affineSpinorPoint_hopf]
  exact (northCoordinates_eq_actualHopf z).symm

theorem projectiveHopf_affine_hasFDerivAt_north :
    HasFDerivAt
      (fun z : ℂ => (projectiveHopf (affineSpinorPoint z)).1)
      northDifferential 0 := by
  convert northCoordinates_hasFDerivAt_zero using 1
  funext z
  exact projectiveHopf_affine_coordinates z

theorem affineSpinorPoint_eq_projectiveChart (z : ℂ) :
    affineSpinorPoint z = (projectiveChart 1 0).symm ![z] := by
  rw [projectiveChart_symm_apply]
  unfold affineSpinorPoint euclideanPoint homogeneousVector
  congr 1
  funext i
  fin_cases i <;> simp

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthDerivative
