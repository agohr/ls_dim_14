import QuaternionicSymmetry.FourDimensionalExteriorCanonicalHodge
import Mathlib.LinearAlgebra.Matrix.Orthogonal

/-! Finite bilinear averaging is invariant under the actual orthogonal
rank-three transition. This is the algebraic overlap ingredient for the
canonical four-dimensional exterior Hodge operator. -/

namespace QuaternionicSymmetry.FourDimensionalHodgeOrthogonalSum

open Matrix
open scoped BigOperators
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem bilinear_sum_orthogonal
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R * Rᵀ = 1)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (x y : Fin 3 → V) :
    (∑ s : Fin 3,
      B (∑ t : Fin 3, R t s • x t)
        (∑ u : Fin 3, R u s • y u)) =
      ∑ t : Fin 3, B (x t) (y t) := by
  have hdot (t u : Fin 3) :
      (∑ s : Fin 3, R t s * R u s) = if t = u then 1 else 0 := by
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A t u) hR
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  calc
    _ = ∑ s : Fin 3, ∑ t : Fin 3, ∑ u : Fin 3,
          R t s * R u s * B (x u) (y t) := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [map_sum, LinearMap.sum_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul]
      simp [Finset.sum_mul, Finset.mul_sum]
      congr 1
      funext t
      congr 1
      funext u
      ring
    _ = ∑ t : Fin 3, ∑ u : Fin 3,
          (∑ s : Fin 3, R t s * R u s) * B (x u) (y t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_mul]
    _ = _ := by
      simp [hdot]

end
end QuaternionicSymmetry.FourDimensionalHodgeOrthogonalSum
