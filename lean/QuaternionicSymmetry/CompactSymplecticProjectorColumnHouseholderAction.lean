import QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderUnit
import QuaternionicSymmetry.CompactSymplecticProjectorColumnReflection

/-! A concrete compact-symplectic Householder reflection sends the base
complex column to the negative of a unit real-first-pair representative. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderAction

open Matrix CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnHouseholderNorm
open CompactSymplecticProjectorColumnHouseholderUnit
open CompactSymplecticProjectorColumnReflection
open CompactSymplecticProjectorReflection
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := EuclideanSpace ℂ (I n)

theorem householderReflection_firstColumn (n : ℕ)
    (w : Metric.sphere (0 : V n) 1) (r : ℝ)
    (hfirst : w.1 (Sum.inl 0) = (r : ℂ))
    (hsecond : w.1 (Sum.inr 0) = 0)
    (hw : w.1 ≠ baseColumn n) (i : I n) :
    (unitColumnReflection n (householderUnit n w hw)).1.1 i (Sum.inl 0) =
      -w.1 i := by
  let t : ℝ := ‖baseColumn n - w.1‖
  have ht : t ≠ 0 := by
    dsimp [t]
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw.symm)
  have htsq : (t : ℂ) * t = 2 * (1 - (r : ℂ)) := by
    have h := householder_difference_norm_sq n w r hfirst
    change t ^ 2 = 2 * (1 - r) at h
    exact_mod_cast (show t * t = 2 * (1 - r) by simpa only [pow_two] using h)
  have hcoef : (2 : ℂ) * ((t : ℂ)⁻¹ * (1 - (r : ℂ)) * (t : ℂ)⁻¹) = 1 := by
    field_simp [show (t : ℂ) ≠ 0 by exact_mod_cast ht]
    linear_combination -htsq
  let z := householderUnit n w hw
  have hzi (k : I n) : z.1 k = (t : ℂ)⁻¹ * ((baseColumn n) k - w.1 k) := by
    simp [z, t, householderUnit_apply, smul_eq_mul]
  have hz0 : z.1 (Sum.inl 0) = (t : ℂ)⁻¹ * (1 - (r : ℂ)) := by
    rw [hzi, hfirst]
    simp [baseColumn, EuclideanSpace.single_apply]
  have hz1 : z.1 (Sum.inr 0) = 0 := by
    rw [hzi, hsecond]
    simp [baseColumn, EuclideanSpace.single_apply]
  have hm0 : pairedColumn n ((EuclideanSpace.equiv (I n) ℂ) z.1) (Sum.inl 0) = 0 := by
    simp [pairedColumn, hz1]
  change (reflectionMatrix (columnProjector n
      ((EuclideanSpace.equiv (I n) ℂ) z.1))) i (Sum.inl 0) = -w.1 i
  simp only [reflectionMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
    columnProjector]
  rw [hm0]
  simp only [star_zero, mul_zero, add_zero]
  change (z.1 i * star (z.1 (Sum.inl 0)) +
    z.1 i * star (z.1 (Sum.inl 0)) -
    (if i = Sum.inl (0 : Fin (n + 1)) then 1 else 0)) = -w.1 i
  rw [hz0, hzi]
  have hstar_t : star ((t : ℂ)⁻¹) = (t : ℂ)⁻¹ := by simp
  have hstar_r : star (1 - (r : ℂ)) = 1 - (r : ℂ) := by simp
  simp only [StarMul.star_mul, hstar_t, hstar_r]
  calc
    _ = ((2 : ℂ) * ((t : ℂ)⁻¹ * (1 - (r : ℂ)) * (t : ℂ)⁻¹)) *
          ((baseColumn n) i - w.1 i) -
          (if i = Sum.inl (0 : Fin (n + 1)) then 1 else 0) := by ring
    _ = -w.1 i := by
      rw [hcoef]
      by_cases hi : i = Sum.inl (0 : Fin (n + 1))
      · subst i
        simp [baseColumn, EuclideanSpace.single_apply]
      · simp [hi, baseColumn, EuclideanSpace.single_apply]

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderAction
