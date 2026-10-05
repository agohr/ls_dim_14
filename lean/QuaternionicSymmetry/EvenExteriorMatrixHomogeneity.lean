import QuaternionicSymmetry.QuaternionicExteriorEvenTrace
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-! Homogeneous matrix powers in the commutative even exterior algebra. -/
namespace QuaternionicSymmetry.EvenExteriorMatrixHomogeneity
open QuaternionicExteriorEvenTrace EvenForms ExteriorContinuousPairing
noncomputable section

variable {V κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Fintype κ] [DecidableEq κ]

private abbrev X := ExteriorAlgebra ℝ (Module.Dual ℝ V)

private theorem matrix_pow_mem (d m : ℕ)
    (A : Matrix κ κ (EvenAlgebra V))
    (hA : ∀ i j, ((A i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ d (Module.Dual ℝ V))
    (i j : κ) :
    (((A ^ m) i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ (d * m) (Module.Dual ℝ V) := by
  induction m generalizing i j with
  | zero =>
      change (((1 : Matrix κ κ (EvenAlgebra V)) i j : EvenAlgebra V) : X (V := V)) ∈ _
      classical
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
  | succ m ih =>
      rw [pow_succ, Matrix.mul_apply]
      change ((∑ k : κ, (A ^ m) i k * A k j : EvenAlgebra V) : X (V := V)) ∈ _
      rw [Nat.mul_succ]
      change (Subalgebra.val (evenSubalgebra ℝ (Module.Dual ℝ V))
        (∑ k : κ, (A ^ m) i k * A k j)) ∈ _
      rw [map_sum]
      apply Submodule.sum_mem
      intro k hk
      rw [map_mul]
      exact SetLike.mul_mem_graded (ih i k) (hA k j)

theorem matrix_trace_pow_mem (d m : ℕ)
    (A : Matrix κ κ (EvenAlgebra V))
    (hA : ∀ i j, ((A i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ d (Module.Dual ℝ V)) :
    ((Matrix.trace (A ^ m) : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ (d * m) (Module.Dual ℝ V) := by
  rw [Matrix.trace]
  change ((∑ i : κ, (A ^ m) i i : EvenAlgebra V) : X (V := V)) ∈ _
  change (Subalgebra.val (evenSubalgebra ℝ (Module.Dual ℝ V))
    (∑ i : κ, (A ^ m) i i)) ∈ _
  rw [map_sum]
  exact Submodule.sum_mem _ (fun i hi => matrix_pow_mem d m A hA i i)

end
end QuaternionicSymmetry.EvenExteriorMatrixHomogeneity
