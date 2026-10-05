import QuaternionicSymmetry.CompactSymplecticProjectorColumnContinuity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The first complex column of every actual compact-symplectic matrix is a
unit vector, with the Euclidean inner product (not the function sup norm). -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFirstColumnUnit

open Matrix CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnContinuity
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

def firstColumnEuclidean (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) : EuclideanSpace ℂ (I n) :=
  (EuclideanSpace.equiv (I n) ℂ).symm (firstColumn n u)

theorem firstColumnEuclidean_inner_self (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    inner ℂ (firstColumnEuclidean n u) (firstColumnEuclidean n u) = 1 := by
  have h := inner_matrix_col_col (u.1.1 : Matrix (I n) (I n) ℂ)
    (u.1.1 : Matrix (I n) (I n) ℂ) (Sum.inl 0) (Sum.inl 0)
  rw [show (u.1.1 : Matrix (I n) (I n) ℂ)ᴴ * u.1.1 = 1 from by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.UnitaryGroup.star_mul_self u.1] at h
  simpa [firstColumnEuclidean, firstColumn] using h

theorem firstColumnEuclidean_norm (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    ‖firstColumnEuclidean n u‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), firstColumnEuclidean_inner_self]
  norm_num

def firstColumnSphere (n : ℕ) (u : CompactSymplecticHaar.Group (n + 1)) :
    Metric.sphere (0 : EuclideanSpace ℂ (I n)) 1 :=
  ⟨firstColumnEuclidean n u, mem_sphere_zero_iff_norm.mpr
    (firstColumnEuclidean_norm n u)⟩

theorem continuous_firstColumnSphere (n : ℕ) :
    Continuous (firstColumnSphere n) := by
  apply Continuous.subtype_mk
  exact (EuclideanSpace.equiv (I n) ℂ).symm.continuous.comp
    (continuous_firstColumn n)

end
end QuaternionicSymmetry.CompactSymplecticProjectorFirstColumnUnit
