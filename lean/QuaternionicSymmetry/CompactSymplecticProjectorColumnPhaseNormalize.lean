import QuaternionicSymmetry.CompactSymplecticProjectorColumnPhase

/-! A unit quaternionic phase makes the first paired complex coordinate of
any column real and nonnegative, without changing its line projector. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnPhaseNormalize

noncomputable section

theorem exists_unit_phase_first_pair_real (A B : ℂ) :
    ∃ (a b : ℂ) (r : ℝ), 0 ≤ r ∧
      star a * a + star b * b = 1 ∧
      a * A - b * star B = (r : ℂ) ∧
      a * B + b * star A = 0 := by
  let s : ℝ := Complex.normSq A + Complex.normSq B
  have hs : 0 ≤ s := add_nonneg (Complex.normSq_nonneg A) (Complex.normSq_nonneg B)
  by_cases hzero : s = 0
  · have hAn : Complex.normSq A = 0 := by
      dsimp [s] at hzero
      nlinarith [Complex.normSq_nonneg A, Complex.normSq_nonneg B]
    have hBn : Complex.normSq B = 0 := by
      dsimp [s] at hzero
      nlinarith [Complex.normSq_nonneg A, Complex.normSq_nonneg B]
    have hA : A = 0 := Complex.normSq_eq_zero.mp hAn
    have hB : B = 0 := Complex.normSq_eq_zero.mp hBn
    refine ⟨1, 0, 0, by norm_num, ?_, ?_, ?_⟩ <;> simp [hA, hB]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hzero)
    let r : ℝ := Real.sqrt s
    have hrpos : 0 < r := Real.sqrt_pos.2 hspos
    have hr2 : r * r = s := by
      dsimp [r]
      exact Real.mul_self_sqrt hs
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
    have hsum : (s : ℂ) = star A * A + star B * B := by
      simp only [s, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self,
        Complex.star_def]
    have hr2c : (r : ℂ) * r = (s : ℂ) := by exact_mod_cast hr2
    have hnorm : star A * A + star B * B = (r : ℂ) * r := hsum.symm.trans hr2c.symm
    refine ⟨star A / (r : ℂ), -B / (r : ℂ), r, le_of_lt hrpos, ?_, ?_, ?_⟩
    · have hstar_r : star (r : ℂ) = (r : ℂ) := by simp
      simp only [div_eq_mul_inv, star_mul, star_inv₀, hstar_r, star_star,
        star_neg]
      calc
        _ = (star A * A + star B * B) * ((r : ℂ)⁻¹ * (r : ℂ)⁻¹) := by ring
        _ = 1 := by rw [hnorm]; field_simp [hrc]
    · simp only [div_eq_mul_inv]
      calc
        _ = (star A * A + star B * B) * (r : ℂ)⁻¹ := by ring
        _ = (r : ℂ) := by rw [hnorm]; field_simp [hrc]
    · simp only [div_eq_mul_inv]
      ring

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnPhaseNormalize
