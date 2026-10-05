import QuaternionicSymmetry.HolomorphicLineSheafTensor
import QuaternionicSymmetry.HolomorphicLineCoreClassGroup
import Mathlib.Algebra.Group.TransferInstance

/-! The group of genuine locally free rank-one sheaf isomorphism classes.
Group laws are inherited through the reconstructed bundle equivalence,
and multiplication is proved to be the actual sheafified tensor product.
Thus this is a multiplicative geometric comparison, not merely a group
structure on an unrelated set. Cohomological Picard computation is separate. -/

namespace QuaternionicSymmetry.HolomorphicLineSheafClassGroup

open CategoryTheory Manifold
open HolomorphicLineSheafClasses HolomorphicLineSheafTensor
open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

instance : CommGroup (SheafClass (B := B) IB) := (classEquiv IB).symm.commGroup

/-- The bundle/sheaf equivalence now preserves multiplication, whose
genuine sheaf tensor interpretation is checked in `class_mul`. -/
def classMulEquiv : CoreClass.{0} (B := B) IB ≃* SheafClass (B := B) IB :=
  (Equiv.mulEquiv (classEquiv IB).symm).symm

@[simp] theorem classMulEquiv_apply (a : CoreClass.{0} (B := B) IB) :
    classMulEquiv IB a = classEquiv IB a := rfl

/-- Multiplication is the isomorphism class of the actual tensor sheaf. -/
theorem class_mul (S T : LineSheaf (B := B) IB) :
    (Quotient.mk _ S : SheafClass IB) * Quotient.mk _ T =
      Quotient.mk _ (tensorLineSheaf IB S T) := by
  change (Quotient.mk _
    (toLineSheaf IB ((toLineCore IB S).tensor IB (toLineCore IB T))) : SheafClass IB) = _
  exact Quotient.sound ⟨(tensorRepresentationIso IB S T).symm⟩

/-- The unit is represented by sections of the genuine trivial line. -/
theorem class_one : (1 : SheafClass (B := B) IB) =
    Quotient.mk _ (toLineSheaf IB (trivialLine IB)) := rfl

/-- The inverse is represented by the actual dual of the reconstructed
line bundle; no cohomological identification is used. -/
theorem class_inv (S : LineSheaf (B := B) IB) :
    (Quotient.mk _ S : SheafClass IB)⁻¹ =
      Quotient.mk _ (toLineSheaf IB ((toLineCore IB S).dual IB)) := rfl

end
end QuaternionicSymmetry.HolomorphicLineSheafClassGroup
