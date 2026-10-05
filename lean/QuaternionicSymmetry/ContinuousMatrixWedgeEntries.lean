import QuaternionicSymmetry.ContinuousWedge
import Mathlib.Analysis.Matrix.Normed

/-! Entrywise expansion of a normalized wedge of real matrix-valued forms. -/
namespace QuaternionicSymmetry.ContinuousMatrixWedgeEntries
open QuaternionicSymmetry.ContinuousWedge
noncomputable section
variable {V κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Fintype κ] [DecidableEq κ] {p q : ℕ}

local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

/-- Extract a matrix coefficient of a continuous alternating form. -/
def entry (i j : κ)
    (α : V [⋀^Fin p]→L[ℝ] Matrix κ κ ℝ) : V [⋀^Fin p]→L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j).compContinuousAlternatingMap
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => κ → ℝ) i).compContinuousAlternatingMap α)

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem entry_apply (i j : κ)
    (α : V [⋀^Fin p]→L[ℝ] Matrix κ κ ℝ) (v : Fin p → V) :
    entry i j α v = α v i j := rfl

/-- Matrix multiplication inside the coefficient pairing becomes a finite
sum of scalar wedges on each entry, with no extra factorial. -/
theorem entry_wedge_mul (i j : κ)
    (α : V [⋀^Fin p]→L[ℝ] Matrix κ κ ℝ)
    (β : V [⋀^Fin q]→L[ℝ] Matrix κ κ ℝ) :
    entry i j (wedge (ContinuousLinearMap.mul ℝ (Matrix κ κ ℝ)) α β) =
      ∑ k : κ, wedge (ContinuousLinearMap.mul ℝ ℝ)
        (entry i k α) (entry k j β) := by
  ext v
  simp only [entry_apply, wedge_apply, ContinuousAlternatingMap.sum_apply]
  simp only [ContinuousLinearMap.mul_apply', Matrix.smul_apply, Matrix.sum_apply,
    Matrix.mul_apply, smul_eq_mul, Finset.mul_sum]
  simp only [Finset.smul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

end
end QuaternionicSymmetry.ContinuousMatrixWedgeEntries
