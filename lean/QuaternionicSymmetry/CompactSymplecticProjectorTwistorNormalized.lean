import QuaternionicSymmetry.CompactSymplecticProjectorTwistorScaleLaw

/-! A representative-independent normalized quaternionic-line projector
constructed directly from a nonzero complex column. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorNormalized

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorTwistorScaleLaw

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

def columnNormSq (n : ℕ) (v : V n) : ℂ := (star v) ⬝ᵥ v

theorem columnNormSq_smul (n : ℕ) (t : ℂ) (v : V n) :
    columnNormSq n (t • v) = (star t * t) * columnNormSq n v := by
  simp [columnNormSq, dotProduct, Finset.mul_sum, mul_add,
    mul_comm, mul_left_comm, mul_assoc]

theorem columnNormSq_ne_zero (n : ℕ) {v : V n} (hv : v ≠ 0) :
    columnNormSq n v ≠ 0 := by
  intro hz
  let w : EuclideanSpace ℂ (I n) :=
    (EuclideanSpace.equiv (I n) ℂ).symm v
  have hw : inner ℂ w w = 0 := by
    change v ⬝ᵥ star v = 0
    simpa [columnNormSq, dotProduct, mul_comm] using hz
  have hw0 : w = 0 := inner_self_eq_zero.mp hw
  exact hv (by simpa [w] using congrArg (EuclideanSpace.equiv (I n) ℂ) hw0)

def normalizedProjector (n : ℕ) (v : V n) : Mat n :=
  (columnNormSq n v)⁻¹ • columnProjector n v

theorem normalizedProjector_smul (n : ℕ) (t : ℂ) (v : V n)
    (ht : t ≠ 0) :
    normalizedProjector n (t • v) = normalizedProjector n v := by
  classical
  have ha : star t * t ≠ 0 := mul_ne_zero (by simpa using ht) ht
  simp only [normalizedProjector, columnNormSq_smul, columnProjector_smul,
    smul_smul]
  rw [mul_inv_rev]
  rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorNormalized
