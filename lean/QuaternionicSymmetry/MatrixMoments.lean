import Mathlib.Analysis.Matrix.Order
import QuaternionicSymmetry.SumSymmetry

/-! The numerical matrix positivity calculation in Chapter 8.

The matrices here have complex entries, not differential-form entries.
This is one finite-dimensional step in the Gaussian moment argument.
-/

namespace QuaternionicSymmetry.MatrixMoments

open Matrix
open scoped ComplexOrder MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A PSD matrix gives nonnegative real trace when weighted by a Hermitian square. -/
theorem trace_weighted_square_nonneg {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.IsHermitian) :
    0 ≤ (Matrix.trace (A * B ^ 2)).re := by
  have h := (hA.conjTranspose_mul_mul_same B).trace_nonneg
  rw [hB.eq, ← Matrix.trace_mul_cycle A B B, Matrix.mul_assoc, ← pow_two] at h
  exact (Complex.nonneg_iff.mp h).1

/-- The real symmetric matrix used as the Gaussian covariance in Chapter 8. -/
noncomputable def covarianceEntry {α : Type*} (A : Matrix ι ι ℂ)
    (B : α → Matrix ι ι ℂ) (a b : α) : ℝ :=
  (Matrix.trace (A * (B a * B b + B b * B a))).re / 2

omit [DecidableEq ι] in
/-- The trace of a product of Hermitian matrices is real, even without commutativity. -/
theorem trace_mul_real {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((Matrix.trace (A * B)).re : ℂ) = Matrix.trace (A * B) := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace (A * B)) = Matrix.trace (A * B)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
    Matrix.trace_mul_comm]

omit [DecidableEq ι] in
/-- Taking the real part in the covariance definition loses no component. -/
theorem covarianceEntry_complex {α : Type*} (A : Matrix ι ι ℂ)
    (B : α → Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : ∀ a, (B a).IsHermitian) (a b : α) :
    (covarianceEntry A B a b : ℂ) =
      Matrix.trace (A * (B a * B b + B b * B a)) / 2 := by
  have hab : (B a * B b + B b * B a).IsHermitian := by
    change (B a * B b + B b * B a)ᴴ = B a * B b + B b * B a
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      (hB a).eq, (hB b).eq, add_comm]
  unfold covarianceEntry
  rw [Complex.ofReal_div, trace_mul_real hA hab, Complex.ofReal_ofNat]

omit [DecidableEq ι] in
theorem covarianceEntry_symm {α : Type*} (A : Matrix ι ι ℂ)
    (B : α → Matrix ι ι ℂ) (a b : α) :
    covarianceEntry A B a b = covarianceEntry A B b a := by
  simp only [covarianceEntry, add_comm]

/-- The covariance matrix indexed by a finite family of Hermitian matrices. -/
noncomputable def covarianceMatrix {α : Type*} (A : Matrix ι ι ℂ)
    (B : α → Matrix ι ι ℂ) : Matrix α α ℝ :=
  fun a b => covarianceEntry A B a b

/-- A real linear combination of the matrices in the family. -/
noncomputable def weightedSum {α : Type*} (B : α → Matrix ι ι ℂ) (x : α →₀ ℝ) : Matrix ι ι ℂ :=
  x.sum fun a r => (r : ℂ) • B a

omit [Fintype ι] [DecidableEq ι] in
theorem weightedSum_isHermitian {α : Type*} (B : α → Matrix ι ι ℂ)
    (hB : ∀ a, (B a).IsHermitian) (x : α →₀ ℝ) :
    (weightedSum B x).IsHermitian := by
  classical
  unfold weightedSum
  change (∑ a ∈ x.support, (x a : ℂ) • B a).IsHermitian
  apply isSelfAdjoint_sum
  intro a _
  change ((x a : ℂ) • B a)ᴴ = (x a : ℂ) • B a
  rw [conjTranspose_smul, (hB a).eq]
  have hreal : star (x a : ℂ) = (x a : ℂ) := Complex.conj_ofReal _
  rw [hreal]

theorem covariance_quadratic {α : Type*} (A : Matrix ι ι ℂ)
    (B : α → Matrix ι ι ℂ) (x : α →₀ ℝ) :
    x.sum (fun a ra => x.sum (fun b rb => ra * covarianceMatrix A B a b * rb)) =
      (Matrix.trace (A * (weightedSum B x) ^ 2)).re := by
  classical
  unfold covarianceMatrix covarianceEntry weightedSum
  simp only [Finsupp.sum]
  rw [pow_two]
  rw [← Matrix.mul_assoc]
  simp_rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [Matrix.trace_sum]
  have htrace :
      (∑ i ∈ x.support, (∑ a ∈ x.support,
        A * (x a : ℂ) • B a * (x i : ℂ) • B i).trace) =
        ∑ i ∈ x.support, ∑ a ∈ x.support,
          (A * (x a : ℂ) • B a * (x i : ℂ) • B i).trace := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.trace_sum]
  rw [htrace]
  have hterm (a i : α) :
      (A * ((x a : ℂ) • B a) * ((x i : ℂ) • B i)).trace =
        (x a : ℂ) * (x i : ℂ) * (A * B a * B i).trace := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    ring
  simp_rw [hterm]
  let f : α → α → ℝ := fun a b => (A * B a * B b).trace.re
  have hre (a i : α) :
      ((x a : ℂ) * (x i : ℂ) * (A * B a * B i).trace).re =
        x a * f a i * x i := by
    unfold f
    rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring
  have hinner (i : α) :
      (∑ a ∈ x.support, (x a : ℂ) * (x i : ℂ) * (A * B a * B i).trace).re =
        ∑ a ∈ x.support, x a * f a i * x i := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact hre a i
  rw [Complex.re_sum]
  have hinnerSum :
      (∑ i ∈ x.support, (∑ a ∈ x.support,
        (x a : ℂ) * (x i : ℂ) * (A * B a * B i).trace).re) =
        ∑ i ∈ x.support, ∑ a ∈ x.support, x a * f a i * x i := by
    apply Finset.sum_congr rfl
    intro i _
    exact hinner i
  rw [hinnerSum]
  calc
    _ = ∑ a ∈ x.support, ∑ b ∈ x.support, x a * f a b * x b := by
      simpa only [f, Matrix.mul_add, Matrix.mul_assoc, Matrix.trace_add, Complex.add_re] using
        QuaternionicSymmetry.sum_symmetrized x.support (fun a => x a) f
    _ = ∑ i ∈ x.support, ∑ a ∈ x.support, x a * f a i * x i := by
      rw [Finset.sum_comm]

theorem covarianceMatrix_posSemidef {α : Type*} (A : Matrix ι ι ℂ)
    (B : α → Matrix ι ι ℂ) (hA : A.PosSemidef)
    (hB : ∀ a, (B a).IsHermitian) :
    (covarianceMatrix A B).PosSemidef := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro a b
    simpa [covarianceMatrix] using covarianceEntry_symm A B b a
  · intro x
    change 0 ≤ x.sum (fun a ra => x.sum (fun b rb =>
      ra * covarianceMatrix A B a b * rb))
    rw [covariance_quadratic]
    exact trace_weighted_square_nonneg hA (weightedSum_isHermitian B hB x)


/-- The covariance has the real Gram factorization required for the sum of squares. -/
theorem covarianceMatrix_factorization {α : Type*} [Fintype α]
    (A : Matrix ι ι ℂ) (B : α → Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : ∀ a, (B a).IsHermitian) :
    ∃ C : Matrix α α ℝ, covarianceMatrix A B = C.transpose * C := by
  classical
  let G := covarianceMatrix A B
  have hG : G.PosSemidef := covarianceMatrix_posSemidef A B hA hB
  have hfactor : ∃ C : Matrix α α ℝ, G = star C * C :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hfactor

end QuaternionicSymmetry.MatrixMoments
