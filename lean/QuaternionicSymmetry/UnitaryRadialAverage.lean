import QuaternionicSymmetry.UnitaryHaarMeasure
import QuaternionicSymmetry.UnitaryTransitivity

/-! Haar averaging turns homogeneous functions of a complex vector into
radial functions. This is the transitivity step for unitary column moments. -/

namespace QuaternionicSymmetry.UnitaryRadialAverage

open Matrix MeasureTheory

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem integral_homogeneous (f : (κ → ℂ) → ℝ) (k : ℕ)
    (hf : ∀ (r : ℝ), 0 ≤ r → ∀ z : κ → ℂ, f (r • z) = r ^ k * f z)
    (v : EuclideanSpace ℂ κ) (i₀ : κ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, f ((U : Matrix κ κ ℂ) *ᵥ fun i => v i)
      ∂UnitaryHaarMeasure.probability) =
        ‖v‖ ^ k * ∫ U : Matrix.unitaryGroup κ ℂ,
          f ((U : Matrix κ κ ℂ) *ᵥ Pi.single i₀ 1) ∂UnitaryHaarMeasure.probability := by
  obtain ⟨V, hV⟩ := UnitaryTransitivity.exists_unitary_scaled_column v i₀
  have he (U : Matrix.unitaryGroup κ ℂ) :
      f ((U : Matrix κ κ ℂ) *ᵥ fun i => v i) =
        ‖v‖ ^ k * f (((U * V : Matrix.unitaryGroup κ ℂ) : Matrix κ κ ℂ) *ᵥ
          Pi.single i₀ 1) := by
    rw [hV, Matrix.mulVec_smul, hf _ (norm_nonneg v), Matrix.mulVec_mulVec]
    rfl
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  exact UnitaryHaarMeasure.integral_mul_right
    (fun U : Matrix.unitaryGroup κ ℂ => f ((U : Matrix κ κ ℂ) *ᵥ Pi.single i₀ 1)) V

end
end QuaternionicSymmetry.UnitaryRadialAverage
