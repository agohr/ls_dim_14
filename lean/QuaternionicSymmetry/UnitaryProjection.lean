import QuaternionicSymmetry.UnitaryPolynomialExpectation
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! Concrete Haar-random projections and their polynomial coordinates. -/

namespace QuaternionicSymmetry.UnitaryProjection

open Matrix MvPolynomial
open scoped BigOperators ComplexOrder

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def base (s : Finset κ) : Matrix κ κ ℂ :=
  Matrix.diagonal (fun i => if i ∈ s then 1 else 0)

omit [Fintype κ] in
theorem base_posSemidef (s : Finset κ) : (base s).PosSemidef := by
  rw [base, Matrix.posSemidef_diagonal_iff]
  intro i
  split_ifs <;> norm_num

theorem base_mul_self (s : Finset κ) : base s * base s = base s := by
  rw [base, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem trace_base (s : Finset κ) : Matrix.trace (base s) = (s.card : ℂ) := by
  simp [base, Matrix.trace_diagonal]

def projection (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) : Matrix κ κ ℂ :=
  (U : Matrix κ κ ℂ) * base s * star (U : Matrix κ κ ℂ)

theorem projection_posSemidef (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) :
    (projection s U).PosSemidef :=
  (base_posSemidef s).mul_mul_conjTranspose_same U.val

theorem projection_isHermitian (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) :
    (projection s U).IsHermitian := (projection_posSemidef s U).isHermitian

theorem projection_mul_self (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) :
    projection s U * projection s U = projection s U := by
  change Unitary.conjStarAlgAut ℂ (Matrix κ κ ℂ) U (base s) *
    Unitary.conjStarAlgAut ℂ (Matrix κ κ ℂ) U (base s) =
    Unitary.conjStarAlgAut ℂ (Matrix κ κ ℂ) U (base s)
  rw [← map_mul, base_mul_self]

theorem trace_projection (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) :
    Matrix.trace (projection s U) = (s.card : ℂ) := by
  rw [projection, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, trace_base]

theorem projection_apply (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) (i j : κ) :
    projection s U i j = ∑ a ∈ s, U.val i a * star (U.val j a) := by
  simp only [projection, base, Matrix.mul_apply, Matrix.diagonal, Matrix.of_apply,
    Matrix.star_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp

def coordinate (i j : κ) : MvPolynomial (UnitaryPolynomialExpectation.Variables κ) ℂ :=
  X ((i, j), 0) + C Complex.I * X ((i, j), 1)

def conjugateCoordinate (i j : κ) : MvPolynomial (UnitaryPolynomialExpectation.Variables κ) ℂ :=
  X ((i, j), 0) - C Complex.I * X ((i, j), 1)

theorem eval_coordinate (U : Matrix.unitaryGroup κ ℂ) (i j : κ) :
    (coordinate i j).eval (fun p => (UnitaryPolynomialExpectation.coordinates U p : ℂ)) =
      U.val i j := by
  simp [coordinate, UnitaryPolynomialExpectation.coordinates, mul_comm Complex.I]

theorem eval_conjugateCoordinate (U : Matrix.unitaryGroup κ ℂ) (i j : κ) :
    (conjugateCoordinate i j).eval
      (fun p => (UnitaryPolynomialExpectation.coordinates U p : ℂ)) = star (U.val i j) := by
  apply Complex.ext <;>
    simp [conjugateCoordinate, UnitaryPolynomialExpectation.coordinates]

def matrixPolynomial (s : Finset κ) :
    Matrix κ κ (MvPolynomial (UnitaryPolynomialExpectation.Variables κ) ℂ) :=
  fun i j => ∑ a ∈ s, coordinate i a * conjugateCoordinate j a

theorem eval_matrixPolynomial (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) :
    (matrixPolynomial s).map
      (MvPolynomial.eval (fun p => (UnitaryPolynomialExpectation.coordinates U p : ℂ))) =
        projection s U := by
  ext i j
  simp only [Matrix.map_apply, matrixPolynomial, map_sum, map_mul,
    eval_coordinate, eval_conjugateCoordinate, projection_apply]

end
end QuaternionicSymmetry.UnitaryProjection
