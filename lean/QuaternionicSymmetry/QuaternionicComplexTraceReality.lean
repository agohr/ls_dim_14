import QuaternionicSymmetry.QuaternionicComplexTrace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! A real symmetric operator commuting with the quaternionic complex
structure has real complex trace. The proof uses the imaginary trace as the
real trace of its product with the skew complex structure. -/
namespace QuaternionicSymmetry.QuaternionicComplexTraceReality

open QuaternionicComplexModule QuaternionicComplexTrace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V] (Q : QuaternionicStructure V)

private def IMap : V →ₗ[ℝ] V := Q.I.toLinearEquiv.toLinearMap

omit [Nontrivial V] in
private theorem trace_zero_of_skew (A : V →ₗ[ℝ] V)
    (hA : ∀ v w, inner ℝ (A v) w + inner ℝ v (A w) = 0) :
    LinearMap.trace ℝ V A = 0 := by
  rw [LinearMap.trace_eq_sum_inner A (stdOrthonormalBasis ℝ V)]
  apply Finset.sum_eq_zero
  intro i hi
  have hs := hA ((stdOrthonormalBasis ℝ V) i)
    ((stdOrthonormalBasis ℝ V) i)
  rw [real_inner_comm] at hs
  linarith

omit [FiniteDimensional ℝ V] [Nontrivial V] in
private theorem IMap_mul_commutes (A : V →ₗ[ℝ] V)
    (hA : ∀ v, A (Q.I v) = Q.I (A v)) :
    ∀ v, (IMap Q * A) (Q.I v) = Q.I ((IMap Q * A) v) := by
  intro v
  simp only [Module.End.mul_apply, IMap, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv]
  rw [hA]

omit [FiniteDimensional ℝ V] [Nontrivial V] in
private theorem complexLinearEnd_IMap_mul (A : V →ₗ[ℝ] V)
    (hA : ∀ v, A (Q.I v) = Q.I (A v)) :
    letI : Module ℂ V := complexModule Q;
    complexLinearEnd Q (IMap Q * A) (IMap_mul_commutes Q A hA) =
      Complex.I • complexLinearEnd Q A hA := by
  letI : Module ℂ V := complexModule Q
  ext v
  change Q.I (A v) = Complex.I • A v
  exact (complex_I_smul Q (A v)).symm

theorem complex_trace_im_eq_zero_of_symmetric (A : V →ₗ[ℝ] V)
    (hA : ∀ v, A (Q.I v) = Q.I (A v))
    (hSym : A.IsSymmetric) :
    (letI : Module ℂ V := complexModule Q
     letI : FiniteDimensional ℂ V := complex_finite Q
     LinearMap.trace ℂ V (complexLinearEnd Q A hA)).im = 0 := by
  have hskew : ∀ v w,
      inner ℝ ((IMap Q * A) v) w +
        inner ℝ v ((IMap Q * A) w) = 0 := by
    intro v w
    change inner ℝ (Q.I (A v)) w + inner ℝ v (Q.I (A w)) = 0
    rw [Q.I_skew, hSym v (Q.I w), hA w]
    ring
  have hz := trace_zero_of_skew (IMap Q * A) hskew
  have ht := real_trace_eq_two_complex_trace_re Q (IMap Q * A)
    (IMap_mul_commutes Q A hA)
  rw [hz, complexLinearEnd_IMap_mul Q A hA] at ht
  simp only [map_smul, smul_eq_mul, Complex.I_mul_re] at ht
  linarith

theorem complex_trace_eq_real_of_symmetric (A : V →ₗ[ℝ] V)
    (hA : ∀ v, A (Q.I v) = Q.I (A v))
    (hSym : A.IsSymmetric) :
    (letI : Module ℂ V := complexModule Q
     letI : FiniteDimensional ℂ V := complex_finite Q
     LinearMap.trace ℂ V (complexLinearEnd Q A hA)) =
      ((letI : Module ℂ V := complexModule Q
        letI : FiniteDimensional ℂ V := complex_finite Q
        LinearMap.trace ℂ V (complexLinearEnd Q A hA)).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using complex_trace_im_eq_zero_of_symmetric Q A hA hSym

omit [FiniteDimensional ℝ V] [Nontrivial V] in
theorem square_isSymmetric_of_skew (F : V →ₗ[ℝ] V)
    (hF : ∀ v w, inner ℝ (F v) w + inner ℝ v (F w) = 0) :
    (F ^ 2).IsSymmetric := by
  intro v w
  simp only [pow_two, Module.End.mul_apply]
  have h₁ := hF (F v) w
  have h₂ := hF v (F w)
  linarith

theorem complex_trace_even_power_eq_real_of_skew (F : V →ₗ[ℝ] V)
    (hF : ∀ v, F (Q.I v) = Q.I (F v))
    (hskew : ∀ v w, inner ℝ (F v) w + inner ℝ v (F w) = 0)
    (j : ℕ) :
    (letI : Module ℂ V := complexModule Q
     letI : FiniteDimensional ℂ V := complex_finite Q
     LinearMap.trace ℂ V
       (complexLinearEnd Q ((F ^ 2) ^ j)
         (commutes_I_pow Q (F ^ 2) (commutes_I_pow Q F hF 2) j))).im = 0 :=
  complex_trace_im_eq_zero_of_symmetric Q _ _
    ((square_isSymmetric_of_skew F hskew).pow j)

end
end QuaternionicSymmetry.QuaternionicComplexTraceReality
