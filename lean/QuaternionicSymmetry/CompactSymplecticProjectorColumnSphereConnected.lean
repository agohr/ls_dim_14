import QuaternionicSymmetry.CompactSymplecticProjectorFirstColumnUnit
import Mathlib.Analysis.Normed.Module.Connected

/-! The full unit sphere in the concrete complex column space is connected.
This statement alone does not assert that the column-projector map lands in
the symplectic orbit; the completion/surjectivity theorem is still required. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnSphereConnected

open QuaternionicMatrixModel
noncomputable section

private abbrev V (n : ℕ) := EuclideanSpace ℂ (Fin (n + 1) ⊕ Fin (n + 1))

theorem column_real_rank_gt_one (n : ℕ) : 1 < Module.rank ℝ (V n) := by
  rw [← Module.finrank_eq_rank]
  rw [real_finrank_eq_four_mul]
  exact_mod_cast (by omega : 1 < 4 * (n + 1))

theorem unit_column_sphere_connected (n : ℕ) :
    IsConnected (Metric.sphere (0 : V n) 1) :=
  isConnected_sphere (column_real_rank_gt_one n) 0 (by norm_num)

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnSphereConnected
