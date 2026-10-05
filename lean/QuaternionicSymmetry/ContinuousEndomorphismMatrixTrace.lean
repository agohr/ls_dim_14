import QuaternionicSymmetry.ContinuousEndomorphismMatrix
import QuaternionicSymmetry.ExteriorMatrixTraceBridge
import QuaternionicSymmetry.LocalEndomorphismTrace

/-! Real trace is the matrix trace in any fixed real basis, as an equality of
continuous linear functionals. -/
namespace QuaternionicSymmetry.ContinuousEndomorphismMatrixTrace
open Module ContinuousEndomorphismMatrix
noncomputable section

variable {V κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype κ] [DecidableEq κ]

local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

theorem trace_factor_apply (b : Basis κ ℝ V) (T : V →L[ℝ] V) :
    LocalEndomorphismTrace.traceCLM T =
      ExteriorMatrixTraceBridge.traceCLM (matrixCLM b T) := by
  rw [LocalEndomorphismTrace.traceCLM_apply,
    ExteriorMatrixTraceBridge.traceCLM_apply, matrixCLM_apply]
  exact LinearMap.trace_eq_matrix_trace ℝ b T.toLinearMap

end
end QuaternionicSymmetry.ContinuousEndomorphismMatrixTrace
