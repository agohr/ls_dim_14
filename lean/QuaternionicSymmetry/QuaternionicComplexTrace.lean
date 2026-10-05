import QuaternionicSymmetry.QuaternionicComplexModule
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace QuaternionicSymmetry.QuaternionicComplexTrace

open QuaternionicComplexModule
open Module
noncomputable section

private theorem leftMulMatrix_trace (z : ℂ) :
    (Algebra.leftMulMatrix Complex.basisOneI z).trace = 2 * z.re := by
  rw [Matrix.trace, Fin.sum_univ_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, Complex.coe_basisOneI_repr,
    Complex.coe_basisOneI, Complex.mul_re, Complex.mul_im]
  ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V] (Q : QuaternionicStructure V)

private theorem trace_restrictScalars
    (f : letI : Module ℂ V := complexModule Q; V →ₗ[ℂ] V) :
    letI : Module ℂ V := complexModule Q;
    letI : IsScalarTower ℝ ℂ V := complex_scalar_tower Q
    LinearMap.trace ℝ V (f.restrictScalars ℝ) =
      2 * (LinearMap.trace ℂ V f).re := by
  letI : Module ℂ V := complexModule Q
  letI : IsScalarTower ℝ ℂ V := complex_scalar_tower Q
  letI : FiniteDimensional ℂ V := complex_finite Q
  let b := Module.Free.chooseBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower' b),
    LinearMap.restrictScalars_toMatrix Complex.basisOneI b f,
    LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.comp_apply, Matrix.map_apply]
  change ∑ x, (Algebra.leftMulMatrix Complex.basisOneI
      ((LinearMap.toMatrix b b) f x x)).trace = _
  simp_rw [leftMulMatrix_trace]
  rw [← Finset.mul_sum]
  congr 1
  exact (Complex.re_sum _ _).symm

/-- The real trace of a complex-linear real operator is twice the real part
of its complex trace. -/
theorem real_trace_eq_two_complex_trace_re (A : V →ₗ[ℝ] V)
    (hA : ∀ v, A (Q.I v) = Q.I (A v)) :
    LinearMap.trace ℝ V A =
      2 * (letI : Module ℂ V := complexModule Q
           letI : FiniteDimensional ℂ V := complex_finite Q
           LinearMap.trace ℂ V (complexLinearEnd Q A hA)).re := by
  have h := trace_restrictScalars Q (complexLinearEnd Q A hA)
  simpa only [LinearMap.ext_iff, complexLinearEnd_apply] using h

omit [FiniteDimensional ℝ V] [Nontrivial V] in
theorem commutes_I_mul (A B : V →ₗ[ℝ] V)
    (hA : ∀ v, A (Q.I v) = Q.I (A v))
    (hB : ∀ v, B (Q.I v) = Q.I (B v)) :
    ∀ v, (A * B) (Q.I v) = Q.I ((A * B) v) := by
  intro v
  simp only [Module.End.mul_apply, hA, hB]

omit [FiniteDimensional ℝ V] [Nontrivial V] in
theorem commutes_I_neg (A : V →ₗ[ℝ] V)
    (hA : ∀ v, A (Q.I v) = Q.I (A v)) :
    ∀ v, (-A) (Q.I v) = Q.I ((-A) v) := by
  intro v
  simp only [LinearMap.neg_apply, hA, map_neg]

omit [FiniteDimensional ℝ V] [Nontrivial V] in
theorem commutes_I_pow (A : V →ₗ[ℝ] V)
    (hA : ∀ v, A (Q.I v) = Q.I (A v)) (j : ℕ) :
    ∀ v, (A ^ j) (Q.I v) = Q.I ((A ^ j) v) := by
  induction j with
  | zero => intro v; simp
  | succ j hj =>
      simpa [pow_succ] using commutes_I_mul Q (A ^ j) A hj hA

/-- The paper's half-complex trace has quarter-real-trace normalization
after taking the real part. This applies directly to `(-X²)^j`. -/
theorem half_complex_trace_re_eq_quarter_real_trace
    (X : V →ₗ[ℝ] V) (hX : ∀ v, X (Q.I v) = Q.I (X v)) (j : ℕ) :
    (1 / 2 : ℝ) *
      (letI : Module ℂ V := complexModule Q
       letI : FiniteDimensional ℂ V := complex_finite Q
       LinearMap.trace ℂ V
         (complexLinearEnd Q ((-(X ^ 2)) ^ j)
           (commutes_I_pow Q (-(X ^ 2))
             (commutes_I_neg Q (X ^ 2)
               (commutes_I_pow Q X hX 2)) j))).re =
    (1 / 4 : ℝ) * LinearMap.trace ℝ V ((-(X ^ 2)) ^ j) := by
  have h := real_trace_eq_two_complex_trace_re Q ((-(X ^ 2)) ^ j)
    (commutes_I_pow Q (-(X ^ 2))
      (commutes_I_neg Q (X ^ 2) (commutes_I_pow Q X hX 2)) j)
  rw [h]
  ring

theorem half_complex_trace_power_re_eq_quarter_real_trace
    (F : V →ₗ[ℝ] V) (hF : ∀ v, F (Q.I v) = Q.I (F v)) (j : ℕ) :
    (1 / 2 : ℝ) *
      (letI : Module ℂ V := complexModule Q
       letI : FiniteDimensional ℂ V := complex_finite Q
       LinearMap.trace ℂ V
         (complexLinearEnd Q ((F ^ 2) ^ j)
           (commutes_I_pow Q (F ^ 2) (commutes_I_pow Q F hF 2) j))).re =
    (1 / 4 : ℝ) * LinearMap.trace ℝ V ((F ^ 2) ^ j) := by
  have h := real_trace_eq_two_complex_trace_re Q ((F ^ 2) ^ j)
    (commutes_I_pow Q (F ^ 2) (commutes_I_pow Q F hF 2) j)
  rw [h]
  ring

omit [FiniteDimensional ℝ V] [Nontrivial V] in
/-- The source's `X = i F / (2π)` converts `-X²` to the positive real
multiple `F²` at the level of complex-linear endomorphisms. -/
theorem source_operator_square
    (A : letI : Module ℂ V := complexModule Q; V →ₗ[ℂ] V) :
    letI : Module ℂ V := complexModule Q;
    -((Complex.I / (2 * (Real.pi : ℂ))) • A) ^ 2 =
      ((1 / (4 * Real.pi ^ 2) : ℝ) : ℂ) • A ^ 2 := by
  letI : Module ℂ V := complexModule Q
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [smul_pow]
  have hs : -((Complex.I / (2 * (Real.pi : ℂ))) ^ 2) =
      ((1 / (4 * Real.pi ^ 2) : ℝ) : ℂ) := by
    push_cast
    field_simp
    norm_num [Complex.I_sq]
  rw [← neg_smul, hs]

omit [FiniteDimensional ℝ V] [Nontrivial V] in
private theorem complexLinearEnd_square (F : V →ₗ[ℝ] V)
    (hF : ∀ v, F (Q.I v) = Q.I (F v)) :
    letI : Module ℂ V := complexModule Q;
    (complexLinearEnd Q F hF) ^ 2 =
      complexLinearEnd Q (F ^ 2) (commutes_I_pow Q F hF 2) := by
  letI : Module ℂ V := complexModule Q
  ext v
  simp [pow_two, Module.End.mul_apply, complexLinearEnd_apply]

/-- Numeric source normalization: with `X = iF/(2π)`, the real part of
the half-complex trace of `(-X²)^j` equals the quarter-real trace of the
actual real endomorphism `F^{2j}`, scaled by `(4π²)^{-j}`. -/
theorem source_half_trace_power_re_eq_real_trace
    (F : V →ₗ[ℝ] V) (hF : ∀ v, F (Q.I v) = Q.I (F v)) (j : ℕ) :
    letI : Module ℂ V := complexModule Q;
    letI : FiniteDimensional ℂ V := complex_finite Q;
    let A := complexLinearEnd Q F hF
    (1 / 2 : ℝ) *
      (LinearMap.trace ℂ V
        ((-((Complex.I / (2 * (Real.pi : ℂ))) • A) ^ 2) ^ j)).re =
      ((1 / (4 * Real.pi ^ 2) : ℝ) ^ j) *
        ((1 / 4 : ℝ) * LinearMap.trace ℝ V ((F ^ 2) ^ j)) := by
  letI : Module ℂ V := complexModule Q
  letI : FiniteDimensional ℂ V := complex_finite Q
  let A := complexLinearEnd Q F hF
  change (1 / 2 : ℝ) *
      (LinearMap.trace ℂ V
        ((-((Complex.I / (2 * (Real.pi : ℂ))) • A) ^ 2) ^ j)).re = _
  rw [source_operator_square Q A, smul_pow]
  rw [map_smul]
  simp only [smul_eq_mul, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hpow : (A ^ 2) ^ j =
      complexLinearEnd Q ((F ^ 2) ^ j)
        (commutes_I_pow Q (F ^ 2) (commutes_I_pow Q F hF 2) j) := by
    induction j with
    | zero => ext v; simp [complexLinearEnd_apply]
    | succ j hj =>
        rw [pow_succ, hj]
        ext v
        simp only [Module.End.mul_apply, complexLinearEnd_apply, pow_succ]
        change ((F * F) ^ j) (A (A v)) =
          ((F * F) ^ j) (F (F v))
        rfl
  rw [hpow]
  have h := half_complex_trace_power_re_eq_quarter_real_trace Q F hF j
  calc
    _ = ((1 / (4 * Real.pi ^ 2) : ℝ) ^ j) *
        ((1 / 2 : ℝ) *
          (LinearMap.trace ℂ V
            (complexLinearEnd Q ((F ^ 2) ^ j)
              (commutes_I_pow Q (F ^ 2) (commutes_I_pow Q F hF 2) j))).re) := by ring
    _ = _ := by rw [h]

end
end QuaternionicSymmetry.QuaternionicComplexTrace
