import QuaternionicSymmetry.HolomorphicLineCoreClasses
import QuaternionicSymmetry.HolomorphicLineTensorGroupGauges

/-! The cover-invariant classes of actual represented holomorphic line
cores form a commutative group: tensor is multiplication, the actual trivial
line is the unit and dualization is inverse. This does not yet identify the
classes with every invertible analytic sheaf, compute a Picard group, or
assert that the contact line generates it. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreClassGroup

open HolomorphicLineCoreClasses HolomorphicLineTensorGroupGauges
open scoped Manifold ContDiff
noncomputable section

universe u
variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

def trivialLine : LineCore.{u} (B := B) IB where
  Index := PUnit.{u+1}
  core := trivialCore
  holomorphic := inferInstance

theorem tensor_comm (L M : LineCore.{u} (B := B) IB) :
    Isomorphic IB (L.tensor IB M) (M.tensor IB L) := by
  letI := L.holomorphic
  letI := M.holomorphic
  exact ⟨tensorCommGauge L.core M.core⟩

theorem tensor_assoc (L M N : LineCore.{u} (B := B) IB) :
    Isomorphic IB ((L.tensor IB M).tensor IB N) (L.tensor IB (M.tensor IB N)) := by
  letI := L.holomorphic
  letI := M.holomorphic
  letI := N.holomorphic
  exact ⟨tensorAssocGauge L.core M.core N.core⟩

theorem tensor_trivial (L : LineCore.{u} (B := B) IB) :
    Isomorphic IB (L.tensor IB (trivialLine IB)) L := by
  letI := L.holomorphic
  exact ⟨tensorTrivialGauge L.core⟩

theorem tensor_dual (L : LineCore.{u} (B := B) IB) :
    Isomorphic IB (L.tensor IB (L.dual IB)) (trivialLine IB) := by
  letI := L.holomorphic
  exact ⟨tensorDualTrivialGauge L.core⟩

instance : CommGroup (CoreClass.{u} (B := B) IB) where
  mul := CoreClass.tensor IB
  one := Quotient.mk _ (trivialLine IB)
  inv := CoreClass.dual IB
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with
    | h L =>
      induction b using Quotient.inductionOn with
      | h M =>
        induction c using Quotient.inductionOn with
        | h N => exact Quotient.sound (tensor_assoc IB L M N)
  mul_comm := by
    intro a b
    induction a using Quotient.inductionOn with
    | h L =>
      induction b using Quotient.inductionOn with
      | h M => exact Quotient.sound (tensor_comm IB L M)
  mul_one := by
    intro a
    induction a using Quotient.inductionOn with
    | h L => exact Quotient.sound (tensor_trivial IB L)
  one_mul := by
    intro a
    induction a using Quotient.inductionOn with
    | h L =>
      exact (Quotient.sound (tensor_comm IB (trivialLine IB) L)).trans
        (Quotient.sound (tensor_trivial IB L))
  inv_mul_cancel := by
    intro a
    induction a using Quotient.inductionOn with
    | h L =>
      exact (Quotient.sound (tensor_comm IB (L.dual IB) L)).trans
        (Quotient.sound (tensor_dual IB L))

@[simp] theorem class_mul (L M : LineCore.{u} (B := B) IB) :
    (Quotient.mk _ L : CoreClass IB) * Quotient.mk _ M =
      Quotient.mk _ (L.tensor IB M) := rfl

@[simp] theorem class_inv (L : LineCore.{u} (B := B) IB) :
    (Quotient.mk _ L : CoreClass IB)⁻¹ = Quotient.mk _ (L.dual IB) := rfl

theorem class_eq_iff_isomorphic (L M : LineCore.{u} (B := B) IB) :
    (Quotient.mk _ L : CoreClass IB) = Quotient.mk _ M ↔ Isomorphic IB L M :=
  Quotient.eq

end
end QuaternionicSymmetry.HolomorphicLineCoreClassGroup
