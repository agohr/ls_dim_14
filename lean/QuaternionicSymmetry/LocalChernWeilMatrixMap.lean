import QuaternionicSymmetry.ContinuousMatrixWedgeMap
import QuaternionicSymmetry.LocalChernWeilTracePowers

/-! Matrix coordinates of all recursively normalized local curvature powers. -/
namespace QuaternionicSymmetry.LocalChernWeilMatrixMap
open ContinuousWedge ContinuousMatrixWedgeMap
  LocalChernWeilTracePowers LocalConnectionForms DifferentialFormCoefficient
noncomputable section

variable {E R κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R] [Fintype κ] [DecidableEq κ]

local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

/-- Wedge powers of the matrix coordinates of an actual curvature two-form,
indexed by the same degree as `curvaturePowerForm`. -/
def mappedPower (f : R →L[ℝ] Matrix κ κ ℝ)
    (Γ : LocalConnection.Form (E := E) (A := R)) (x : E) :
    (k : ℕ) → E [⋀^Fin (powerDegree k)]→L[ℝ] Matrix κ κ ℝ
  | 0 => f.compContinuousAlternatingMap (curvatureForm Γ x)
  | k + 1 => wedge (ContinuousLinearMap.mul ℝ (Matrix κ κ ℝ))
      (f.compContinuousAlternatingMap (curvatureForm Γ x))
      (mappedPower f Γ x k)

/-- Matrix coordinates preserve every actual curvature wedge power. -/
theorem map_curvaturePowerForm (f : R →L[ℝ] Matrix κ κ ℝ)
    (hmul : ∀ a b : R, f (a * b) = f a * f b)
    (Γ : LocalConnection.Form (E := E) (A := R)) (x : E) (k : ℕ) :
    f.compContinuousAlternatingMap (curvaturePowerForm Γ k x) =
      mappedPower f Γ x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change f.compContinuousAlternatingMap
        (wedge (ContinuousLinearMap.mul ℝ R) (curvatureForm Γ x)
          (curvaturePowerForm Γ k x)) = _
      rw [map_wedge f hmul, ih]
      rfl

end
end QuaternionicSymmetry.LocalChernWeilMatrixMap
