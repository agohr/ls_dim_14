import QuaternionicSymmetry.RealToComplexTangentComplexificationLinear
import Mathlib.Algebra.Lie.BaseChange

/-! Bracket preservation survives the literal real-to-complex tensor extension.
This is algebraic; the bracket-preserving real map in applications is the
internally proved derivative of an actual smooth Lie-group homomorphism. -/

namespace QuaternionicSymmetry.ComplexifiedLieBracketTransfer

open RealToComplexTangentComplexification
open scoped TensorProduct
noncomputable section

variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L]
  [LieRing V] [LieAlgebra ℂ V]

theorem complexifiedMapComplex_map_lie (f : L →ₗ[ℝ] V)
    (hBracket : ∀ x y : L, f ⁅x,y⁆ = ⁅f x,f y⁆)
    (x y : ℂ ⊗[ℝ] L) :
    complexifiedMapComplex f ⁅x,y⁆ =
      ⁅complexifiedMapComplex f x, complexifiedMapComplex f y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero =>
          have h : ⁅a ⊗ₜ[ℝ] u, (0 : ℂ ⊗[ℝ] L)⁆ = 0 := by
            simp [LieAlgebra.ExtendScalars.instBracketTensorProduct]
          simp only [h, map_zero]
          exact (lie_zero _).symm
      | tmul b v =>
          simp only [LieAlgebra.ExtendScalars.bracket_tmul,
            complexifiedMapComplex_tmul, hBracket, mul_smul, smul_lie,
            lie_smul]
          rw [smul_comm]
      | add y z hy hz =>
          have h : ⁅a ⊗ₜ[ℝ] u, y + z⁆ =
              ⁅a ⊗ₜ[ℝ] u, y⁆ + ⁅a ⊗ₜ[ℝ] u, z⁆ := by
            simp [LieAlgebra.ExtendScalars.instBracketTensorProduct]
          rw [h, map_add, map_add, lie_add, hy, hz]
  | add x z hx hz =>
      simp only [add_lie, map_add, hx, hz]

end
end QuaternionicSymmetry.ComplexifiedLieBracketTransfer
