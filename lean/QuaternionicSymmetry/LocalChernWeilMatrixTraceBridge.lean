import QuaternionicSymmetry.LocalChernWeilMatrixMap
import QuaternionicSymmetry.ExteriorMatrixTraceBridge

/-! Compatibility between the two identical recursive degree conventions and
their matrix-valued wedge powers. -/
namespace QuaternionicSymmetry.LocalChernWeilMatrixTraceBridge
open LocalChernWeilTracePowers LocalChernWeilMatrixMap
  ExteriorMatrixWedgeBridge ContinuousWedge
noncomputable section

variable {E R κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R] [Fintype κ] [DecidableEq κ]

local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

theorem degree_eq (k : ℕ) : powerDegree k = wedgeDegree k := by
  rfl

theorem mappedPower_eq (f : R →L[ℝ] Matrix κ κ ℝ)
    (Γ : LocalConnection.Form (E := E) (A := R)) (x : E)
    (γ : E [⋀^Fin 2]→L[ℝ] Matrix κ κ ℝ)
    (hγ : f.compContinuousAlternatingMap (LocalConnectionForms.curvatureForm Γ x) = γ)
    (k : ℕ) : mappedPower f Γ x k = matrixWedgePower γ k := by
  induction k with
  | zero => simp [mappedPower, matrixWedgePower, hγ]
  | succ k ih =>
      change
        (wedge (ContinuousLinearMap.mul ℝ (Matrix κ κ ℝ))
          (f.compContinuousAlternatingMap (LocalConnectionForms.curvatureForm Γ x))
          (mappedPower f Γ x k))
        = (wedge (ContinuousLinearMap.mul ℝ (Matrix κ κ ℝ)) γ
          (matrixWedgePower γ k))
      rw [hγ]
      rw [ih]

end
end QuaternionicSymmetry.LocalChernWeilMatrixTraceBridge
