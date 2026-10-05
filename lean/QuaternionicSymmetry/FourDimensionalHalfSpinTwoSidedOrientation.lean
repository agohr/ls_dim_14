import QuaternionicSymmetry.FourDimensionalHalfSpinLeftOrientation
import QuaternionicSymmetry.FourDimensionalHalfSpinOrthogonalImageAction

/-! The checked two-sided quaternionic real isometries all preserve the
quaternionic orientation on `ℍ`. This proves containment in the oriented
orthogonal group; equality with the full `SO(4)` remains unproved. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedOrientation

open scoped Quaternion
open FourDimensionalHalfSpinTwoSidedOrthogonal
  FourDimensionalHalfSpinRightOrientation
  FourDimensionalHalfSpinLeftOrientation
  QuaternionicProjectiveStandardHilbertStructure

noncomputable section

theorem twoSidedIsometry_det_pos (q r : unitary ℍ) :
    0 < LinearMap.det (twoSidedIsometry q r : ℍ →ₗ[ℝ] ℍ) := by
  have heq : (twoSidedIsometry q r : ℍ →ₗ[ℝ] ℍ) =
      (leftUnitIsometry q : ℍ →ₗ[ℝ] ℍ).comp
        (rightUnitIsometry r : ℍ →ₗ[ℝ] ℍ) := rfl
  rw [heq, LinearMap.det_comp]
  exact mul_pos (leftUnitIsometry_det_pos q)
    (rightUnitIsometry_det_pos r)

/-- The concrete image of `Sp(1)×Sp(1)` lies in the orientation-preserving
orthogonal subgroup, with the determinant sign certified by actual frames. -/
theorem orthogonalImage_det_pos
    (g : FourDimensionalHalfSpinOrthogonalImageAction.orthogonalImage) :
    0 < LinearMap.det (g.1 : ℍ →ₗ[ℝ] ℍ) := by
  obtain ⟨p,hp⟩ := g.2
  rw [← hp]
  exact twoSidedIsometry_det_pos p.1 p.2

end
end QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedOrientation
