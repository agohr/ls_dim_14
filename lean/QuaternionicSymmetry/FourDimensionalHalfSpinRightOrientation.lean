import QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedOrthogonal
import QuaternionicSymmetry.FourDimensionalQuaternionicPointwiseOrientation

/-! Right unit-quaternion multiplication preserves the actual quaternionic
orientation on the real four-space `ℍ`. It carries the standard quaternionic
orthonormal frame at `1` to the frame at `r*`; the pre-existing frame
orientation theorem supplies the determinant sign. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinRightOrientation

open scoped Quaternion
open FourDimensionalHalfSpinTwoSidedOrthogonal
  FourDimensionalQuaternionicHodgeFrame
  FourDimensionalQuaternionicOrientation
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicUnitQuaternionTransport

noncomputable section

private theorem quaternion_finrank : Module.finrank ℝ ℍ = 4 := by
  simpa using Quaternion.finrank_eq_four

private theorem norm_star_unit (r : unitary ℍ) : ‖star (r : ℍ)‖ = 1 := by
  rw [Quaternion.norm_star]
  have hn := Quaternion.normSq_eq_norm_mul_self (r : ℍ)
  rw [QuaternionicUnitScalarIsometries.normSq_one_of_unitary] at hn
  nlinarith [norm_nonneg (r : ℍ)]

private theorem right_frame (r : unitary ℍ) (i : Fin 4) :
    rightUnitIsometry r
      (frameBasis leftLineStructure quaternion_finrank 1 (by simp) i) =
    frameBasis leftLineStructure quaternion_finrank
      (star (r : ℍ)) (norm_star_unit r) i := by
  rw [frameBasis_apply, frameBasis_apply]
  fin_cases i <;>
    simp [QuaternionicStructure.frame, leftLineStructure,
      leftLineI, leftLineJ, leftUnitIsometry_apply,
      rightUnitIsometry_apply, mul_assoc]

theorem rightUnitIsometry_det_pos (r : unitary ℍ) :
    0 < LinearMap.det (rightUnitIsometry r : ℍ →ₗ[ℝ] ℍ) := by
  let b := (frameBasis leftLineStructure quaternion_finrank 1 (by simp)).toBasis
  let c := (frameBasis leftLineStructure quaternion_finrank
    (star (r : ℍ)) (norm_star_unit r)).toBasis
  have hmap : b.map (rightUnitIsometry r).toLinearEquiv = c := by
    apply DFunLike.ext
    intro i
    exact right_frame r i
  have hor := frame_orientation_eq leftLineStructure quaternion_finrank
    1 (star (r : ℍ)) (by simp) (norm_star_unit r)
  apply (Module.Basis.orientation_comp_linearEquiv_eq_iff_det_pos b
    (rightUnitIsometry r).toLinearEquiv).mp
  rw [hmap]
  exact hor.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinRightOrientation
