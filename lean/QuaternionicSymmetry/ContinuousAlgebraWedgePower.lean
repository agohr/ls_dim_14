import QuaternionicSymmetry.ContinuousMatrixWedgeMap
import QuaternionicSymmetry.ExteriorMatrixWedgeBridge

/-! Ordered normalized powers of an arbitrary algebra-valued two-form, and
their transport through multiplicative matrix coordinates. -/
namespace QuaternionicSymmetry.ContinuousAlgebraWedgePower
open ContinuousWedge ContinuousMatrixWedgeMap
  ExteriorMatrixWedgeBridge LocalChernWeilTracePowers
noncomputable section

variable {E R κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R] [Fintype κ] [DecidableEq κ]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

def orderedPower (F : E [⋀^Fin 2]→L[ℝ] R) :
    (k : ℕ) → E [⋀^Fin (powerDegree k)]→L[ℝ] R
  | 0 => F
  | k + 1 => wedge (ContinuousLinearMap.mul ℝ R) F (orderedPower F k)

theorem map_orderedPower (f : R →L[ℝ] Matrix κ κ ℝ)
    (hmul : ∀ a b : R, f (a * b) = f a * f b)
    (F : E [⋀^Fin 2]→L[ℝ] R)
    (γ : E [⋀^Fin 2]→L[ℝ] Matrix κ κ ℝ)
    (hγ : f.compContinuousAlternatingMap F = γ)
    (k : ℕ) :
    f.compContinuousAlternatingMap (orderedPower F k) =
      matrixWedgePower γ k := by
  induction k with
  | zero => exact hγ
  | succ k ih =>
      change f.compContinuousAlternatingMap
        (wedge (ContinuousLinearMap.mul ℝ R) F (orderedPower F k)) = _
      rw [map_wedge f hmul, hγ, ih]
      rfl

end
end QuaternionicSymmetry.ContinuousAlgebraWedgePower
