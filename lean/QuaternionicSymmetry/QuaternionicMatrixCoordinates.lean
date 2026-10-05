import QuaternionicSymmetry.QuaternionicCanonicalModel
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Complex matrix coordinates for real endomorphisms commuting with the
standard quaternionic complex structure. -/
namespace QuaternionicSymmetry.QuaternionicMatrixCoordinates
open QuaternionicMatrixModel
open scoped Matrix
noncomputable section

theorem complex_smul_decompose {n : ℕ} (z : ℂ) (v : V n) :
    z • v = z.re • v + z.im • (Complex.I • v) := by
  conv_lhs => rw [← z.re_add_im]
  simp only [add_smul, mul_smul, Complex.coe_smul]

def complexEnd {n : ℕ} (A : V n →ₗ[ℝ] V n)
    (hI : ∀ v, A (standardI n v) = standardI n (A v)) : V n →ₗ[ℂ] V n where
  toFun := A
  map_add' := A.map_add
  map_smul' z v := by
    change A (z • v) = z • A v
    rw [complex_smul_decompose z v, complex_smul_decompose z (A v),
      A.map_add, A.map_smul, A.map_smul]
    change z.re • A v + z.im • A (standardI n v) = _
    rw [hI]
    rfl

def matrixEnd {n : ℕ} (A : V n →ₗ[ℝ] V n)
    (hI : ∀ v, A (standardI n v) = standardI n (A v)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.toEuclideanLin.symm (complexEnd A hI)

theorem matrixEnd_action {n : ℕ} (A : V n →ₗ[ℝ] V n)
    (hI : ∀ v, A (standardI n v) = standardI n (A v)) (v : V n) :
    realMatrixAction (matrixEnd A hI) v = A v := by
  change Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm (complexEnd A hI)) v = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem matrixEnd_commutes_J {n : ℕ} (A : V n →ₗ[ℝ] V n)
    (hI : ∀ v, A (standardI n v) = standardI n (A v))
    (hJ : ∀ v, A (standardJ n v) = standardJ n (A v)) :
    matrixEnd A hI * CompactSymplecticHaar.standardJ n =
      CompactSymplecticHaar.standardJ n * (matrixEnd A hI).map star := by
  apply (matrix_commutes_J_iff_vector_action n _).2
  intro v
  have hv := hJ (WithLp.toLp 2 v)
  rw [← matrixEnd_action A hI, ← matrixEnd_action A hI] at hv
  have he := congrArg (fun w : V n => w.ofLp) hv
  simpa only [realMatrixAction_apply, standardJ_matrix_action, WithLp.ofLp_toLp] using he

theorem complexEnd_skew_inner {n : ℕ} (A : V n →ₗ[ℝ] V n)
    (hI : ∀ v, A (standardI n v) = standardI n (A v))
    (hskew : ∀ v w, inner ℝ (A v) w + inner ℝ v (A w) = 0) (v w : V n) :
    inner ℂ (complexEnd A hI v) w + inner ℂ v (complexEnd A hI w) = 0 := by
  apply Complex.ext
  · simpa only [Complex.add_re, Complex.zero_re, complexEnd,
      LinearMap.coe_mk, AddHom.coe_mk, ← real_inner_eq_complex_re] using hskew v w
  · have h := hskew v (standardI n w)
    rw [hI] at h
    simp only [real_inner_eq_complex_re, standardI_apply, inner_smul_right,
      Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h
    change (inner ℂ (A v) w + inner ℂ v (A w)).im = (0 : ℂ).im
    simp only [Complex.add_im, Complex.zero_im]
    linarith

theorem matrixEnd_conjTranspose {n : ℕ} (A : V n →ₗ[ℝ] V n)
    (hI : ∀ v, A (standardI n v) = standardI n (A v))
    (hskew : ∀ v w, inner ℝ (A v) w + inner ℝ v (A w) = 0) :
    (matrixEnd A hI)ᴴ = -matrixEnd A hI := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, map_neg]
  have he : Matrix.toEuclideanLin (matrixEnd A hI) = complexEnd A hI :=
    LinearEquiv.apply_symm_apply _ _
  rw [he]
  apply LinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro w
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ (complexEnd A hI w) v = inner ℂ w (-(complexEnd A hI v))
  rw [inner_neg_right]
  exact eq_neg_of_add_eq_zero_left (complexEnd_skew_inner A hI hskew w v)

theorem matrixEnd_symplectic {n : ℕ} (A : V n →ₗ[ℝ] V n)
    (hI : ∀ v, A (standardI n v) = standardI n (A v))
    (hJ : ∀ v, A (standardJ n v) = standardJ n (A v))
    (hskew : ∀ v w, inner ℝ (A v) w + inner ℝ v (A w) = 0) :
    (matrixEnd A hI)ᵀ * CompactSymplecticHaar.standardJ n +
      CompactSymplecticHaar.standardJ n * matrixEnd A hI = 0 := by
  let B := matrixEnd A hI
  let J := CompactSymplecticHaar.standardJ n
  have hs : B.map star = -Bᵀ := by
    rw [← Matrix.conjTranspose_transpose, matrixEnd_conjTranspose A hI hskew]
    rfl
  have hc : B * J = J * B.map star := matrixEnd_commutes_J A hI hJ
  rw [hs, mul_neg] at hc
  have hJ2 : J * J = -1 := CompactSymplecticHaar.standardJ_sq n
  have ht : Bᵀ = J * B * J := by
    have hh := congrArg (fun T => J * T) hc
    change J * (B * J) = J * -(J * Bᵀ) at hh
    rw [mul_neg, ← mul_assoc J J Bᵀ, hJ2] at hh
    simpa only [neg_mul, one_mul, neg_neg, mul_assoc] using hh.symm
  change Bᵀ * J + J * B = 0
  rw [ht]
  simp only [mul_assoc, hJ2, mul_neg, mul_one, neg_add_cancel]

theorem matrixEnd_hermitianAntiSelfDual {n : ℕ} (A : V n →ₗ[ℝ] V n)
    (hI : ∀ v, A (standardI n v) = standardI n (A v))
    (hJ : ∀ v, A (standardJ n v) = standardJ n (A v))
    (hskew : ∀ v w, inner ℝ (A v) w + inner ℝ v (A w) = 0) :
    HermitianAntiSelfDual (Complex.I • matrixEnd A hI) := by
  constructor
  · rw [Matrix.conjTranspose_smul, matrixEnd_conjTranspose A hI hskew]
    simp
  · simp only [smul_smul, Complex.I_mul_I, neg_one_smul, Matrix.transpose_neg,
      neg_mul, mul_neg, ← neg_add, matrixEnd_symplectic A hI hJ hskew, neg_zero]

end
end QuaternionicSymmetry.QuaternionicMatrixCoordinates
