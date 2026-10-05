import QuaternionicSymmetry.FourDimensionalForms
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A determinant-normalized volume coefficient for the four-dimensional calculation. -/

namespace QuaternionicSymmetry.FourDimensionalForms

noncomputable section

/-- Determinant in degree four and zero in every other degree. -/
def volumeAlternating (n : ℕ) : V [⋀^Fin n]→ₗ[ℝ] ℝ :=
  if h : n = 4 then by subst n; exact Matrix.detRowAlternating else 0

/-- The oriented top-degree coefficient, extended linearly to the exterior algebra. -/
def volumeCoefficient : E →ₗ[ℝ] ℝ :=
  ExteriorAlgebra.liftAlternating volumeAlternating

theorem vol_eq_product : vol = ExteriorAlgebra.ιMulti ℝ 4 e := by
  simp [ExteriorAlgebra.ιMulti_succ_apply, vol, g, mul_assoc, Matrix.vecTail]

@[simp] theorem volumeCoefficient_vol : volumeCoefficient vol = 1 := by
  rw [vol_eq_product]
  change ExteriorAlgebra.liftAlternating volumeAlternating
    (ExteriorAlgebra.ιMulti ℝ 4 e) = 1
  rw [ExteriorAlgebra.liftAlternating_apply_ιMulti]
  have he : e = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    simp [e, Matrix.one_apply, eq_comm]
  simp only [volumeAlternating, ↓reduceDIte, he]
  exact Matrix.det_one

theorem vol_ne_zero : vol ≠ 0 := by
  intro h
  have hv := volumeCoefficient_vol
  rw [h, map_zero] at hv
  exact zero_ne_one hv

/-- In the given oriented orthonormal coordinates, the signed square is nonnegative. -/
theorem signed_square_volume (c : ℝ) :
    volumeCoefficient (-((c • α) ^ 2)) = 2 * c ^ 2 := by
  rw [scaled_alpha_sq, map_neg, map_smul, volumeCoefficient_vol]
  simp

theorem signed_square_nonneg (c : ℝ) :
    0 ≤ volumeCoefficient (-((c • α) ^ 2)) := by
  rw [signed_square_volume]
  positivity

theorem quaternionic_volume_coefficient :
    volumeCoefficient (ωI ^ 2 + ωJ ^ 2 + ωK ^ 2) = 6 := by
  rw [omega_sum_sq, map_smul, volumeCoefficient_vol]
  simp

end
end QuaternionicSymmetry.FourDimensionalForms
