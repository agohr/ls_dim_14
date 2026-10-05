import QuaternionicSymmetry.CompactSymplecticProjectorColumnReflection

/-! Right quaternionic unit scalars rotate the complex representative of a
quaternionic line without changing its rank-two projector. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnPhase

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnAlgebra
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

def phaseRotate (n : ℕ) (a b : ℂ) (v : I n → ℂ) : I n → ℂ :=
  a • v + b • pairedColumn n v

theorem pairedColumn_phaseRotate (n : ℕ) (a b : ℂ) (v : I n → ℂ) :
    pairedColumn n (phaseRotate n a b v) =
      star a • pairedColumn n v - star b • v := by
  simp [phaseRotate, pairedColumn_add, pairedColumn_smul,
    pairedColumn_pair, smul_neg, sub_eq_add_neg]

theorem columnProjector_phaseRotate (n : ℕ) (a b : ℂ) (v : I n → ℂ)
    (hab : star a * a + star b * b = 1) :
    columnProjector n (phaseRotate n a b v) = columnProjector n v := by
  ext i j
  unfold columnProjector
  rw [pairedColumn_phaseRotate]
  simp only [phaseRotate, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, star_add, star_sub, star_mul, star_star]
  calc
    _ = (star a * a + star b * b) *
        (v i * star (v j) + pairedColumn n v i * star (pairedColumn n v j)) := by
          ring
    _ = _ := by rw [hab]; ring

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnPhase
