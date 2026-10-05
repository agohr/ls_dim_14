import QuaternionicSymmetry.ContinuousMatrixWedgeEntries

/-! A continuous multiplicative coordinate map commutes with normalized
matrix-valued wedge products. -/
namespace QuaternionicSymmetry.ContinuousMatrixWedgeMap
open ContinuousWedge
noncomputable section

variable {V R κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedRing R] [NormedAlgebra ℝ R] [Fintype κ] [DecidableEq κ]
  {p q : ℕ}

local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

theorem map_wedge (f : R →L[ℝ] Matrix κ κ ℝ)
    (hmul : ∀ a b : R, f (a * b) = f a * f b)
    (α : V [⋀^Fin p]→L[ℝ] R) (β : V [⋀^Fin q]→L[ℝ] R) :
    f.compContinuousAlternatingMap (wedge (ContinuousLinearMap.mul ℝ R) α β) =
      wedge (ContinuousLinearMap.mul ℝ (Matrix κ κ ℝ))
        (f.compContinuousAlternatingMap α) (f.compContinuousAlternatingMap β) := by
  apply ContinuousAlternatingMap.ext
  intro v
  change f (wedge (ContinuousLinearMap.mul ℝ R) α β v) = _
  simp only [wedge_apply, map_smul, map_sum, ContinuousLinearMap.mul_apply']
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h]
    simp [hmul]
  · rw [h]
    simp [hmul]

end
end QuaternionicSymmetry.ContinuousMatrixWedgeMap
