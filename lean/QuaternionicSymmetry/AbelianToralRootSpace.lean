import QuaternionicSymmetry.AbelianLieSpanSubalgebra
import Mathlib.Algebra.Lie.Weights.Cartan

/-! A commuting complex span is nilpotent, so its exact adjoint weight
space lies in the corresponding generalized root space. This makes no
Cartan or diagonalizability claim. -/

namespace QuaternionicSymmetry.AbelianToralRootSpace

open AbelianLieSpanSubalgebra
noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  (S : Set L) (hComm : ∀ x ∈ S, ∀ y ∈ S, ⁅x,y⁆ = 0)

abbrev H : LieSubalgebra ℂ L := lieSubalgebra S hComm

theorem H_isLieAbelian : IsLieAbelian (H S hComm) := by
  refine ⟨fun x y => ?_⟩
  apply Subtype.ext
  exact lieSubalgebra_abelian S hComm x y

theorem H_isNilpotent : LieRing.IsNilpotent (H S hComm) := by
  letI : IsLieAbelian (H S hComm) := H_isLieAbelian S hComm
  infer_instance

theorem exactWeightSpace_le_rootSpace (χ : H S hComm → ℂ) :
    letI := H_isNilpotent S hComm
    LieModule.weightSpace L χ ≤ LieAlgebra.rootSpace (H S hComm) χ := by
  letI : LieRing.IsNilpotent (H S hComm) := H_isNilpotent S hComm
  exact LieModule.weightSpace_le_genWeightSpace L χ

end
end QuaternionicSymmetry.AbelianToralRootSpace
