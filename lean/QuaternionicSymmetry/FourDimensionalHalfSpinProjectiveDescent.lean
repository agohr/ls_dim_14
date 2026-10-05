import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGenerator

/-! The infinitesimal matrix action descends to projective tangent space:
scalar endomorphisms act trivially.  These are identities for the genuine
CP¹ affine-coordinate derivative, not a transported sphere connection. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveDescent

open scoped Matrix Quaternion
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinMatrix

noncomputable section

theorem affineGenerator_add (A B : Mat2) (z : ℂ) :
    affineGenerator (A + B) z =
      affineGenerator A z + affineGenerator B z := by
  simp [affineGenerator, Matrix.add_apply]
  ring

theorem affineGenerator_smul (c : ℂ) (A : Mat2) (z : ℂ) :
    affineGenerator (c • A) z = c * affineGenerator A z := by
  simp [affineGenerator, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The infinitesimal action is insensitive to the center of GL₂(ℂ). -/
theorem affineGenerator_scalar (c z : ℂ) :
    affineGenerator (c • (1 : Mat2)) z = 0 := by
  simp [affineGenerator, Matrix.smul_apply, smul_eq_mul]

theorem affineGenerator_add_scalar (A : Mat2) (c z : ℂ) :
    affineGenerator (A + c • (1 : Mat2)) z = affineGenerator A z := by
  rw [affineGenerator_add, affineGenerator_scalar, add_zero]

/-- A concrete quaternionic Lie-algebra element acts by this quadratic
holomorphic vector field on the honest affine chart of CP¹. -/
theorem affineGenerator_halfSpinMatrix (a : ℍ) (z : ℂ) :
    affineGenerator (halfSpinMatrix a) z =
      second a + (star (first a) - first a) * z +
        star (second a) * z ^ 2 := by
  simp [affineGenerator, halfSpinMatrix]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveDescent
