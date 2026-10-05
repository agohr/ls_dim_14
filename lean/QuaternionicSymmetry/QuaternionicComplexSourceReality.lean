import QuaternionicSymmetry.QuaternionicComplexTraceReality

/-! The numeric source trace itself is real for skew real curvature commuting
with the fixed complex structure. -/
namespace QuaternionicSymmetry.QuaternionicComplexSourceReality
open QuaternionicComplexModule QuaternionicComplexTrace
  QuaternionicComplexTraceReality
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V] (Q : QuaternionicStructure V)

omit [FiniteDimensional ℝ V] [Nontrivial V] in
private theorem complexLinearEnd_pow (F : V →ₗ[ℝ] V)
    (hF : ∀ v, F (Q.I v) = Q.I (F v)) (j : ℕ) :
    letI : Module ℂ V := complexModule Q;
    (complexLinearEnd Q F hF) ^ j =
      complexLinearEnd Q (F ^ j) (commutes_I_pow Q F hF j) := by
  letI : Module ℂ V := complexModule Q
  induction j with
  | zero => ext v; simp [complexLinearEnd_apply]
  | succ j hj =>
      rw [pow_succ, hj]
      ext v
      simp [Module.End.mul_apply, complexLinearEnd_apply, pow_succ]

theorem source_trace_im_zero_of_skew
    (F : V →ₗ[ℝ] V) (hF : ∀ v, F (Q.I v) = Q.I (F v))
    (hskew : ∀ v w, inner ℝ (F v) w + inner ℝ v (F w) = 0)
    (j : ℕ) :
    (letI : Module ℂ V := complexModule Q
     letI : FiniteDimensional ℂ V := complex_finite Q
     let A := complexLinearEnd Q F hF
     LinearMap.trace ℂ V
       ((-((Complex.I / (2 * (Real.pi : ℂ))) • A) ^ 2) ^ j)).im = 0 := by
  letI : Module ℂ V := complexModule Q
  letI : FiniteDimensional ℂ V := complex_finite Q
  let A := complexLinearEnd Q F hF
  change (LinearMap.trace ℂ V
      ((-((Complex.I / (2 * (Real.pi : ℂ))) • A) ^ 2) ^ j)).im = 0
  rw [source_operator_square Q A, smul_pow, map_smul]
  have hA2 : A ^ 2 = complexLinearEnd Q (F ^ 2)
      (commutes_I_pow Q F hF 2) := complexLinearEnd_pow Q F hF 2
  rw [hA2, complexLinearEnd_pow]
  have him := complex_trace_even_power_eq_real_of_skew Q F hF hskew j
  let c : ℝ := 1 / (4 * Real.pi ^ 2)
  let z : ℂ := LinearMap.trace ℂ V
    (complexLinearEnd Q ((F ^ 2) ^ j)
      (commutes_I_pow Q (F ^ 2) (commutes_I_pow Q F hF 2) j))
  change (((c : ℂ) ^ j * z).im) = 0
  have hz : z.im = 0 := him
  have hc : ((c : ℂ) ^ j).im = 0 := by
    simpa only [← Complex.ofReal_pow] using Complex.ofReal_im (c ^ j)
  simp [Complex.mul_im, hc, hz]

theorem source_half_trace_eq_real_trace_of_skew
    (F : V →ₗ[ℝ] V) (hF : ∀ v, F (Q.I v) = Q.I (F v))
    (hskew : ∀ v w, inner ℝ (F v) w + inner ℝ v (F w) = 0)
    (j : ℕ) :
    letI : Module ℂ V := complexModule Q;
    letI : FiniteDimensional ℂ V := complex_finite Q;
    let A := complexLinearEnd Q F hF
    (1 / 2 : ℂ) *
      LinearMap.trace ℂ V
        ((-((Complex.I / (2 * (Real.pi : ℂ))) • A) ^ 2) ^ j) =
      (((1 / (4 * Real.pi ^ 2) : ℝ) ^ j) *
        ((1 / 4 : ℝ) * LinearMap.trace ℝ V ((F ^ 2) ^ j)) : ℂ) := by
  letI : Module ℂ V := complexModule Q
  letI : FiniteDimensional ℂ V := complex_finite Q
  let A := complexLinearEnd Q F hF
  let c : ℝ := 1 / (4 * Real.pi ^ 2)
  change (1 / 2 : ℂ) * LinearMap.trace ℂ V
      ((-((Complex.I / (2 * (Real.pi : ℂ))) • A) ^ 2) ^ j) =
    (((c ^ j) * ((1 / 4 : ℝ) * LinearMap.trace ℝ V ((F ^ 2) ^ j))) : ℂ)
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf]
  apply Complex.ext
  · have hr := source_half_trace_power_re_eq_real_trace Q F hF j
    simpa only [← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      mul_zero, zero_mul, sub_zero, c, A] using hr
  · have him := source_trace_im_zero_of_skew Q F hF hskew j
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_im, Complex.mul_im, him, mul_zero, zero_mul,
      add_zero, A]

end
end QuaternionicSymmetry.QuaternionicComplexSourceReality
