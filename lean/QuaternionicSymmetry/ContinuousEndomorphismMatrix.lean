import QuaternionicSymmetry.LocalChernWeilMatrixMap
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Fixed real-basis matrix coordinates for continuous endomorphisms,
including multiplicativity and trace preservation. -/
namespace QuaternionicSymmetry.ContinuousEndomorphismMatrix
open Module
noncomputable section

variable {V κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype κ] [DecidableEq κ]

local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

def matrixLinear (b : Basis κ ℝ V) : (V →L[ℝ] V) →ₗ[ℝ] Matrix κ κ ℝ where
  toFun T := LinearMap.toMatrix b b T.toLinearMap
  map_add' T U := by simp
  map_smul' r T := by simp

def matrixCLM (b : Basis κ ℝ V) : (V →L[ℝ] V) →L[ℝ] Matrix κ κ ℝ :=
  (matrixLinear b).toContinuousLinearMap

@[simp] theorem matrixCLM_apply (b : Basis κ ℝ V) (T : V →L[ℝ] V) :
    matrixCLM b T = LinearMap.toMatrix b b T.toLinearMap := rfl

theorem matrixCLM_mul (b : Basis κ ℝ V) (T U : V →L[ℝ] V) :
    matrixCLM b (T * U) = matrixCLM b T * matrixCLM b U := by
  change LinearMap.toMatrix b b (T * U).toLinearMap =
    LinearMap.toMatrix b b T.toLinearMap * LinearMap.toMatrix b b U.toLinearMap
  exact LinearMap.toMatrix_mul b T.toLinearMap U.toLinearMap

end
end QuaternionicSymmetry.ContinuousEndomorphismMatrix
