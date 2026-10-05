import Mathlib.Analysis.Fourier.AddCircle
import QuaternionicSymmetry.TorusCharacterInput

/-! Continuous circle characters are integer powers.

This proves `TorusCharacterInput.CircleCharacterSource` from mathlib, with no
literature premise. Fourier completeness gives a nonzero coefficient; Haar
translation invariance then identifies the character with that Fourier mode.
The proof was first checked in contract-audit experiment E11. -/
namespace QuaternionicSymmetry.TorusCharacterFromMathlib
open MeasureTheory AddCircle
open scoped ComplexConjugate
noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem exists_nonzero_fourierCoeff (f : C(AddCircle (1 : ℝ), ℂ))
    (hf : f 0 ≠ 0) : ∃ m : ℤ, fourierCoeff f m ≠ 0 := by
  by_contra h
  push_neg at h
  have hsum : Summable (fourierCoeff f) := by
    have heq : fourierCoeff f = (fun _ : ℤ => (0 : ℂ)) := funext h
    rw [heq]
    exact summable_zero
  have hs := has_pointwise_sum_fourier_series_of_summable hsum (0 : AddCircle (1 : ℝ))
  simp only [h, zero_smul] at hs
  exact hf (hs.unique hasSum_zero)

theorem fourier_translate (m : ℤ) (a x : AddCircle (1 : ℝ)) :
    fourier m (a+x) = fourier m a * fourier m x := by
  simp only [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

theorem character_is_fourier (f : C(AddCircle (1 : ℝ), ℂ))
    (hadd : ∀ a x, f (a+x) = f a * f x) (hzero : f 0 = 1) :
    ∃ m : ℤ, ∀ a, f a = fourier m a := by
  obtain ⟨m, hm⟩ := exists_nonzero_fourierCoeff f (by rw [hzero]; exact one_ne_zero)
  refine ⟨m, ?_⟩
  intro a
  have htrans :
      fourierCoeff f m = (fourier (-m) a * f a) * fourierCoeff f m := by
    calc
      fourierCoeff f m =
          ∫ x : AddCircle (1 : ℝ), fourier (-m) (a+x) * f (a+x) ∂haarAddCircle := by
        simpa only [fourierCoeff, smul_eq_mul] using
          (integral_add_left_eq_self
            (μ := (haarAddCircle : Measure (AddCircle (1 : ℝ))))
            (fun x => fourier (-m) x * f x) a).symm
      _ = ∫ x : AddCircle (1 : ℝ),
          (fourier (-m) a * f a) * (fourier (-m) x * f x) ∂haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [fourier_translate, hadd]
        ring
      _ = (fourier (-m) a * f a) * fourierCoeff f m := by
        rw [integral_const_mul]
        rfl
  have hfactor : fourier (-m) a * f a = 1 := by
    apply mul_right_cancel₀ hm
    simpa only [one_mul] using htrans.symm
  have hunit : fourier m a * fourier (-m) a = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  calc
    f a = (fourier m a * fourier (-m) a) * f a := by rw [hunit, one_mul]
    _ = fourier m a * (fourier (-m) a * f a) := mul_assoc _ _ _
    _ = fourier m a := by rw [hfactor, mul_one]

/-- Exact original source predicate, with no literature hypotheses. -/
theorem circleCharacterSource : QuaternionicSymmetry.TorusCharacterInput.CircleCharacterSource := by
  intro χ
  let f : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x => (χ (toCircle x) : ℂ),
      continuous_subtype_val.comp (χ.continuous.comp continuous_toCircle)⟩
  have hadd : ∀ a x, f (a+x) = f a * f x := by
    intro a x
    change (χ (toCircle (a+x)) : ℂ) = (χ (toCircle a) : ℂ) * (χ (toCircle x) : ℂ)
    rw [toCircle_add, map_mul, Circle.coe_mul]
  have hzero : f 0 = 1 := by simp [f]
  obtain ⟨m, hm⟩ := character_is_fourier f hadd hzero
  refine ⟨m, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := (homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective z
  rw [homeomorphCircle_apply] at ha
  apply Subtype.ext
  have h := hm a
  simpa only [f, ContinuousMap.coe_mk, fourier_apply, toCircle_zsmul, ha] using h

end
end QuaternionicSymmetry.TorusCharacterFromMathlib
