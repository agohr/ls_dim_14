import QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderNorm

/-! The normalized Householder difference is an actual Euclidean unit column. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderUnit

open CompactSymplecticProjectorColumnHouseholderNorm
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := EuclideanSpace ℂ (I n)

def householderUnit (n : ℕ)
    (w : Metric.sphere (0 : V n) 1)
    (hw : w.1 ≠ baseColumn n) : Metric.sphere (0 : V n) 1 := by
  let x := baseColumn n - w.1
  have hx : x ≠ 0 := sub_ne_zero.mpr hw.symm
  have ht : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let z : V n := ‖x‖⁻¹ • x
  have hz : ‖z‖ = 1 := by
    simp [z, norm_smul, inv_mul_cancel₀ ht]
  exact ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩

theorem householderUnit_apply (n : ℕ)
    (w : Metric.sphere (0 : V n) 1) (hw : w.1 ≠ baseColumn n) (i : I n) :
    (householderUnit n w hw).1 i =
      (‖baseColumn n - w.1‖⁻¹ : ℝ) • ((baseColumn n - w.1) i) := by
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderUnit
