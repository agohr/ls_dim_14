import QuaternionicSymmetry.CompactSymplecticProjectorColumnAlgebra

/-! The algebraic scalar norm of a concrete Euclidean unit complex column. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnUnit

open Matrix CompactSymplecticProjectorFirstColumn
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

theorem column_dot_self_eq_inner (n : ℕ) (v : EuclideanSpace ℂ (I n)) :
    (fun i => star (v i)) ⬝ᵥ (fun i => v i) = inner ℂ v v := by
  simp only [dotProduct, PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply]

theorem unit_column_dot_self (n : ℕ)
    (v : Metric.sphere (0 : EuclideanSpace ℂ (I n)) 1) :
    (fun i => star (v.1 i)) ⬝ᵥ (fun i => v.1 i) = 1 := by
  rw [column_dot_self_eq_inner, inner_self_eq_norm_sq_to_K]
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  simp [hn]

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnUnit
