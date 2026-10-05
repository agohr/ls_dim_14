import QuaternionicSymmetry.ComplexGaussianCoordinates
import QuaternionicSymmetry.ComplexGaussianRankOne
import QuaternionicSymmetry.PolynomialCovariance

/-! Polynomial covariance matrices built from concrete independent complex Gaussian coordinates. -/

namespace QuaternionicSymmetry.ComplexGaussianMatrix

open scoped BigOperators ComplexOrder MatrixOrder
open MvPolynomial

noncomputable section

variable {α κ : Type*} [Fintype α]

/-- The complex Gaussian vector in the `m`th row of a real sample. -/
def gaussianVector (ω : (α × κ) → Fin 2 → ℝ) (m : α) : κ → ℂ :=
  fun i => ComplexGaussianVariable.standardComplex (ω (m, i))

/-- The polynomial matrix `∑ₘ qₘ zₘ zₘᴴ` on the actual real coordinates. -/
def matrixPolynomial (q : α → ℝ) :
    Matrix κ κ (MvPolynomial ((α × κ) × Fin 2) ℂ) :=
  fun i j => ∑ m, C (q m : ℂ) *
    ComplexGaussianCoordinates.coordinate (m, i) *
      ComplexGaussianCoordinates.conjugateCoordinate (m, j)

private def evalReal (ω : (α × κ) → Fin 2 → ℝ) : ((α × κ) × Fin 2) → ℝ :=
  fun p => ω p.1 p.2

omit [Fintype α] in
private theorem eval_coordinate (ω : (α × κ) → Fin 2 → ℝ) (p : α × κ) :
    MvPolynomial.eval (fun r => algebraMap ℝ ℂ (ω r.1 r.2))
        (ComplexGaussianCoordinates.coordinate p) =
      ComplexGaussianVariable.standardComplex (ω p) := by
  exact ComplexGaussianCoordinates.eval_coordinate ω p

omit [Fintype α] in
private theorem eval_conjugateCoordinate (ω : (α × κ) → Fin 2 → ℝ) (p : α × κ) :
    MvPolynomial.eval (fun r => algebraMap ℝ ℂ (ω r.1 r.2))
        (ComplexGaussianCoordinates.conjugateCoordinate p) =
      star (ComplexGaussianVariable.standardComplex (ω p)) := by
  exact ComplexGaussianCoordinates.eval_conjugateCoordinate ω p

/-- Evaluating the polynomial covariance matrix gives its weighted rank-one form. -/
theorem evalMatrix_matrixPolynomial (q : α → ℝ) (ω : (α × κ) → Fin 2 → ℝ) :
    PolynomialCovariance.evalMatrix (matrixPolynomial q) (evalReal ω) =
      ∑ m, q m • ComplexGaussianRankOne.rankOne (gaussianVector ω m) := by
  ext i j
  simp only [PolynomialCovariance.evalMatrix, Matrix.map_apply, matrixPolynomial,
    map_sum, map_mul, eval_C]
  simp only [evalReal]
  rw [Finset.sum_apply i, Finset.sum_apply j]
  simp only [ComplexGaussianRankOne.rankOne_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_coordinate ω (m, i), eval_conjugateCoordinate ω (m, j)]
  simp only [gaussianVector, Complex.real_smul]
  rw [mul_assoc]

/-- Every evaluated polynomial covariance matrix with nonnegative real weights is PSD. -/
theorem evalMatrix_matrixPolynomial_posSemidef (q : α → ℝ) (hq : ∀ m, 0 ≤ q m)
    (ω : (α × κ) → Fin 2 → ℝ) [Fintype κ] :
    (PolynomialCovariance.evalMatrix (matrixPolynomial q) (evalReal ω)).PosSemidef := by
  rw [evalMatrix_matrixPolynomial]
  exact ComplexGaussianRankOne.sum_smul_rankOne_posSemidef q hq (gaussianVector ω)

/-- The PSD conclusion in the flat coordinate space used by `evalMatrix`. -/
theorem evalMatrix_matrixPolynomial_posSemidef_flat (q : α → ℝ) (hq : ∀ m, 0 ≤ q m)
    (x : ((α × κ) × Fin 2) → ℝ) [Fintype κ] :
    (PolynomialCovariance.evalMatrix (matrixPolynomial q) x).PosSemidef := by
  simpa only [evalReal] using
    (evalMatrix_matrixPolynomial_posSemidef q hq (fun p k => x (p, k)))

end
end QuaternionicSymmetry.ComplexGaussianMatrix
