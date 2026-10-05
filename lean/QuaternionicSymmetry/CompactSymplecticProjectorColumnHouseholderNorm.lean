import QuaternionicSymmetry.CompactSymplecticProjectorColumnRealGauge

/-! Norm of the Householder difference between the base unit column and a
unit representative with first paired coordinate `(r,0)`. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderNorm

open CompactSymplecticProjectorColumnRealGauge
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := EuclideanSpace ℂ (I n)

def baseColumn (n : ℕ) : V n := EuclideanSpace.single (Sum.inl 0) 1

theorem baseColumn_norm (n : ℕ) : ‖baseColumn n‖ = 1 := by
  simp [baseColumn, EuclideanSpace.norm_single]

theorem baseColumn_inner (n : ℕ) (w : V n) :
    inner ℂ (baseColumn n) w = w (Sum.inl 0) := by
  simpa [baseColumn] using
    (EuclideanSpace.inner_single_left (Sum.inl (0 : Fin (n + 1))) (1 : ℂ) w)

theorem householder_difference_norm_sq (n : ℕ)
    (w : Metric.sphere (0 : V n) 1) (r : ℝ)
    (hr : w.1 (Sum.inl 0) = (r : ℂ)) :
    ‖baseColumn n - w.1‖ ^ 2 = 2 * (1 - r) := by
  rw [norm_sub_sq (𝕜 := ℂ), baseColumn_norm]
  have hw : ‖w.1‖ = 1 := mem_sphere_zero_iff_norm.mp w.2
  rw [hw, baseColumn_inner, hr]
  simp
  ring

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderNorm
