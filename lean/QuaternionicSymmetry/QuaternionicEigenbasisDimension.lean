import QuaternionicSymmetry.QuaternionicEigenbasisCoordinates
import QuaternionicSymmetry.QuaternionicAction
import Mathlib.Tactic

/-! Cardinality calibration for quaternionic eigenbasis blocks. -/

namespace QuaternionicSymmetry.QuaternionicStructure

noncomputable section

variable {V β : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A finite orthonormal basis indexed by quaternionic four-blocks has the
corresponding real dimension. -/
theorem finrank_eq_four_mul_card_of_orthonormalBasis [Fintype β]
    (b : OrthonormalBasis (β × Fin 4) ℝ V) :
    Module.finrank ℝ V = 4 * Fintype.card β := by
  rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The block index cardinality of an eigenbasis agrees with the intrinsic
quaternionic dimension. -/
theorem card_eq_quaternionicDimension_of_orthonormalBasis [Fintype β]
    (Q : QuaternionicStructure V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V) :
    Fintype.card β = Q.quaternionicDimension := by
  have hb := finrank_eq_four_mul_card_of_orthonormalBasis b
  have hQ := Q.real_finrank
  omega

end
end QuaternionicSymmetry.QuaternionicStructure
