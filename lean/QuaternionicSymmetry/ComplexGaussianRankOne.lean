import QuaternionicSymmetry.ComplexGaussianProduct
import Mathlib.Analysis.Matrix.Order

/-! Positive semidefinite rank-one covariance matrices for complex Gaussian sums. -/

namespace QuaternionicSymmetry.ComplexGaussianRankOne

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {κ β : Type*} [Fintype κ] [Fintype β]

/-- The Hermitian rank-one matrix `v vᴴ`. -/
def rankOne (v : κ → ℂ) : Matrix κ κ ℂ :=
  Matrix.vecMulVec v (star v)

omit [Fintype κ] in
@[simp] theorem rankOne_apply (v : κ → ℂ) (i j : κ) :
    rankOne v i j = v i * star (v j) := by
  simp [rankOne, Matrix.vecMulVec_apply]

theorem rankOne_posSemidef (v : κ → ℂ) : (rankOne v).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star v

private theorem real_smul_rankOne_posSemidef (q : ℝ) (hq : 0 ≤ q) (v : κ → ℂ) :
    (q • rankOne v).PosSemidef := by
  let r : ℂ := (Real.sqrt q : ℂ)
  have hr : r * star r = (q : ℂ) := by
    simp [r, ← Complex.ofReal_mul, Real.mul_self_sqrt hq]
  have h : q • rankOne v = rankOne (r • v) := by
    ext i j
    change (q : ℂ) * (v i * star (v j)) = (r * v i) * star (r * v j)
    rw [StarMul.star_mul]
    rw [show (q : ℂ) = r * star r by exact hr.symm]
    ring
  rw [h]
  exact rankOne_posSemidef _

/-- A finite nonnegative combination of Hermitian rank-one matrices is PSD. -/
theorem sum_smul_rankOne_posSemidef (q : β → ℝ) (hq : ∀ m, 0 ≤ q m)
    (v : β → κ → ℂ) :
    (∑ m, q m • rankOne (v m)).PosSemidef := by
  apply Matrix.posSemidef_sum Finset.univ
  intro m _
  exact real_smul_rankOne_posSemidef (q m) (hq m) (v m)

end
end QuaternionicSymmetry.ComplexGaussianRankOne
