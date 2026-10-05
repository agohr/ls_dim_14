import QuaternionicSymmetry.FourDimensionalTwistorNormalizerQuotient
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The explicit complex two-dimensional half-spin representation of unit
quaternions.  This is genuine complex matrix algebra, not a renamed action
on the twistor coefficient sphere.  The projectivization and its comparison
with the negative-Hodge sphere are separate subsequent steps. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinMatrix

open scoped Quaternion Matrix

/-- The `1,i` coordinate of a quaternion. -/
def first (q : ℍ) : ℂ := ⟨q.re, q.imI⟩

/-- The `j,k` coordinate in the decomposition `q = first q + j * second q`. -/
def second (q : ℍ) : ℂ := ⟨q.imJ, -q.imK⟩

/-- Left quaternion multiplication on the right-complex module `ℍ ≅ ℂ²`.
For `q = a + j b`, the matrix is `[a,-conj b;b,conj a]`. -/
def halfSpinMatrix (q : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![first q, -star (second q); second q, star (first q)]

theorem first_mul (p q : ℍ) :
    first (p*q) = first p * first q - star (second p) * second q := by
  apply Complex.ext <;>
    simp [first, second, Quaternion.re_mul, Quaternion.imI_mul,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem second_mul (p q : ℍ) :
    second (p*q) = second p * first q + star (first p) * second q := by
  apply Complex.ext <;>
    simp [first, second, Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The half-spin matrices preserve quaternion multiplication literally. -/
theorem halfSpinMatrix_mul (p q : ℍ) :
    halfSpinMatrix (p*q) = halfSpinMatrix p * halfSpinMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfSpinMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      first_mul, second_mul, star_mul, star_add, star_sub] <;> ring

theorem halfSpinMatrix_one : halfSpinMatrix (1 : ℍ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfSpinMatrix, first, second, Complex.ext_iff]

/-- The unit quaternion group acts through actual invertible complex
two-by-two matrices. -/
def halfSpinGroupHom : unitary ℍ →* (Matrix (Fin 2) (Fin 2) ℂ)ˣ where
  toFun q := {
    val := halfSpinMatrix q
    inv := halfSpinMatrix (star q)
    val_inv := by
      rw [← halfSpinMatrix_mul, q.property.2, halfSpinMatrix_one]
    inv_val := by
      rw [← halfSpinMatrix_mul, q.property.1, halfSpinMatrix_one] }
  map_one' := by
    apply Units.ext
    exact halfSpinMatrix_one
  map_mul' q r := by
    apply Units.ext
    exact halfSpinMatrix_mul q r

end QuaternionicSymmetry.FourDimensionalHalfSpinMatrix
