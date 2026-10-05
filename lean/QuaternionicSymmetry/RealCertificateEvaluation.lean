import QuaternionicSymmetry.AlgebraCertificates
import Mathlib.Algebra.Algebra.Tower

/-! Evaluating rational certificate generators through a real coefficient
algebra, with the scalar conventions used by the positivity proofs. -/

namespace QuaternionicSymmetry.RealCertificateEvaluation

open AlgebraCertificates

noncomputable section

variable {S : Type*} [CommRing S] [Algebra ℝ S] [Algebra ℚ S] [IsScalarTower ℚ ℝ S]

theorem evaluate_c_real (u z₁ z₂ z₃ z₄ : S) (q : ℚ) :
    evaluate u z₁ z₂ z₃ z₄ (c q) = algebraMap ℝ S (q : ℝ) := by
  rw [evaluate_c, IsScalarTower.algebraMap_apply ℚ ℝ S]
  rfl

theorem evaluate_F₂ (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ F₂ =
      algebraMap ℝ S (1 / 1152) * z₁ ^ 2 + algebraMap ℝ S (1 / 2880) * z₂ := by
  simp only [F₂, map_add, map_mul, map_pow, evaluate_c_real, evaluate_Z₁, evaluate_Z₂,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

theorem evaluate_F₃ (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ F₃ =
      algebraMap ℝ S (1 / 82944) * z₁ ^ 3 + algebraMap ℝ S (1 / 69120) * z₁ * z₂ +
        algebraMap ℝ S (1 / 181440) * z₃ := by
  simp only [F₃, map_add, map_mul, map_pow, evaluate_c_real, evaluate_Z₁, evaluate_Z₂,
    evaluate_Z₃, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

theorem evaluate_F₄ (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ F₄ =
      algebraMap ℝ S (1 / 7962624) * z₁ ^ 4 +
        algebraMap ℝ S (1 / 3317760) * z₁ ^ 2 * z₂ +
        algebraMap ℝ S (1 / 16588800) * z₂ ^ 2 +
        algebraMap ℝ S (1 / 4354560) * z₁ * z₃ +
        algebraMap ℝ S (1 / 9676800) * z₄ := by
  simp only [F₄, map_add, map_mul, map_pow, evaluate_c_real, evaluate_Z₁, evaluate_Z₂,
    evaluate_Z₃, evaluate_Z₄, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

theorem evaluate_M₂₁ (u z₁ z₂ z₃ z₄ : S) (r : ℚ) :
    evaluate u z₁ z₂ z₃ z₄ (M₂₁ r) =
      ((r : ℝ) * (r + 1))⁻¹ • (z₁ ^ 2 + z₂) := by
  simp only [M₂₁, map_add, map_mul, map_pow, evaluate_c_real, evaluate_Z₁, evaluate_Z₂,
    Rat.cast_inv, Rat.cast_mul, Rat.cast_add, Rat.cast_one, one_div, Algebra.smul_def]

theorem evaluate_M₃₁ (u z₁ z₂ z₃ z₄ : S) (r : ℚ) :
    evaluate u z₁ z₂ z₃ z₄ (M₃₁ r) =
      ((r : ℝ) * (r + 1) * (r + 2))⁻¹ • (z₁ ^ 3 + 3 * z₁ * z₂ + 2 * z₃) := by
  simp only [M₃₁, map_add, map_mul, map_pow, evaluate_c_real, evaluate_Z₁, evaluate_Z₂,
    evaluate_Z₃, Rat.cast_inv, Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
    one_div, Algebra.smul_def, map_ofNat]

theorem evaluate_M₃₂ (u z₁ z₂ z₃ z₄ : S) (r : ℚ) :
    evaluate u z₁ z₂ z₃ z₄ (M₃₂ r) =
      (4 / ((r : ℝ) * (r - 1) * (r + 1) * (r + 2))) •
        ((2 * (r : ℝ) + 1) • z₁ ^ 3 + (3 * ((r : ℝ) - 1)) • (z₁ * z₂) +
          ((r : ℝ) - 4) • z₃) := by
  simp only [M₃₂, map_add, map_mul, map_pow, evaluate_c_real, evaluate_Z₁, evaluate_Z₂,
    evaluate_Z₃, Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_sub, Rat.cast_one,
    Rat.cast_ofNat, Algebra.smul_def, mul_assoc]

end
end QuaternionicSymmetry.RealCertificateEvaluation
