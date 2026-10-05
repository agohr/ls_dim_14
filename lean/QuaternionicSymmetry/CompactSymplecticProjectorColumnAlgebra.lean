import QuaternionicSymmetry.CompactSymplecticProjectorColumnSphereMap

/-! Algebra of the forced quaternionic mate of one complex column. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnAlgebra

open Matrix CompactSymplecticProjectorFirstColumn
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

theorem pairedColumn_pair (n : ℕ) (v : I n → ℂ) :
    pairedColumn n (pairedColumn n v) = -v := by
  funext i
  cases i <;> simp [pairedColumn]

theorem pairedColumn_add (n : ℕ) (v w : I n → ℂ) :
    pairedColumn n (v + w) = pairedColumn n v + pairedColumn n w := by
  funext i
  cases i <;> simp [pairedColumn, Pi.add_apply, add_comm]

theorem pairedColumn_smul (n : ℕ) (a : ℂ) (v : I n → ℂ) :
    pairedColumn n (a • v) = star a • pairedColumn n v := by
  funext i
  cases i <;> simp [pairedColumn, Pi.smul_apply]

theorem pairedColumn_orthogonal (n : ℕ) (v : I n → ℂ) :
    (fun i => star (v i)) ⬝ᵥ pairedColumn n v = 0 := by
  classical
  simp only [dotProduct, Fintype.sum_sum_type]
  simp [pairedColumn, mul_comm]

theorem pairedColumn_orthogonal_rev (n : ℕ) (v : I n → ℂ) :
    (fun i => star (pairedColumn n v i)) ⬝ᵥ v = 0 := by
  classical
  simp only [dotProduct, Fintype.sum_sum_type]
  simp [pairedColumn, mul_comm]

theorem pairedColumn_norm_sq (n : ℕ) (v : I n → ℂ) :
    (fun i => star (pairedColumn n v i)) ⬝ᵥ pairedColumn n v =
      (fun i => star (v i)) ⬝ᵥ v := by
  classical
  simp only [dotProduct, Fintype.sum_sum_type]
  simp [pairedColumn, mul_comm]
  ac_rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnAlgebra
