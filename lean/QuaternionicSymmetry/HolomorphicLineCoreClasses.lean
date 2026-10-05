import QuaternionicSymmetry.HolomorphicLineGauge

/-! Isomorphism classes of represented holomorphic line cores, with covers
allowed to vary.  This quotient is genuinely by holomorphic bundle gauges;
it is not asserted to classify every holomorphic line bundle on the base. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreClasses

open QuaternionicSymmetry.HolomorphicLineGauge
open scoped Manifold ContDiff
noncomputable section

universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

/-- A holomorphic complex line core with an arbitrary cover index type
in the selected universe. -/
structure LineCore where
  Index : Type u
  core : VectorBundleCore ℂ B ℂ Index
  holomorphic : core.IsContMDiff IB ∞

/-- Actual holomorphic isomorphism between line cores, allowing their
local trivializing covers to differ. -/
def Isomorphic (L M : LineCore.{u} (B := B) IB) : Prop :=
  letI := L.holomorphic
  letI := M.holomorphic
  Nonempty (GaugeIso (IB := IB) L.core M.core)

instance : Setoid (LineCore.{u} (B := B) IB) where
  r := Isomorphic IB
  iseqv := by
    constructor
    · intro L
      letI := L.holomorphic
      exact ⟨GaugeIso.refl (IB := IB) L.core⟩
    · intro L M h
      letI := L.holomorphic
      letI := M.holomorphic
      obtain ⟨e⟩ := h
      exact ⟨e.symm⟩
    · intro L M N h₁ h₂
      letI := L.holomorphic
      letI := M.holomorphic
      letI := N.holomorphic
      obtain ⟨e⟩ := h₁
      obtain ⟨f⟩ := h₂
      exact ⟨e.trans f⟩

/-- Genuine cover-invariant holomorphic isomorphism classes among the
represented line cores at a fixed universe of cover indices. -/
abbrev CoreClass := Quotient (inferInstance : Setoid (LineCore.{u} (B := B) IB))

/-- Tensor product of two represented holomorphic line cores on the
intersection refinement of their covers. -/
def LineCore.tensor (L M : LineCore.{u} (B := B) IB) : LineCore.{u} (B := B) IB := by
  letI := L.holomorphic
  letI := M.holomorphic
  exact {
    Index := L.Index × M.Index
    core := HolomorphicLineTensor.tensorCore L.core M.core
    holomorphic := inferInstance }

theorem tensor_respects {L L' M M' : LineCore.{u} (B := B) IB}
    (hL : Isomorphic IB L L') (hM : Isomorphic IB M M') :
    Isomorphic IB (L.tensor IB M) (L'.tensor IB M') := by
  letI := L.holomorphic
  letI := L'.holomorphic
  letI := M.holomorphic
  letI := M'.holomorphic
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := hM
  exact ⟨e.tensor f⟩

/-- Tensor product descends to genuine cover-invariant isomorphism
classes, rather than depending on a selected trivializing cover. -/
def CoreClass.tensor (a b : CoreClass.{u} (B := B) IB) :
    CoreClass.{u} (B := B) IB :=
  Quotient.liftOn₂ a b
    (fun L M => Quotient.mk _ (L.tensor IB M))
    (by
      intro L L' M M' hL hM
      exact Quotient.sound (tensor_respects IB hL hM))

/-- The represented dual line core. -/
def LineCore.dual (L : LineCore.{u} (B := B) IB) : LineCore.{u} (B := B) IB := by
  letI := L.holomorphic
  exact {
    Index := L.Index
    core := HolomorphicLineIntegerPowers.dualCore L.core
    holomorphic := inferInstance }

theorem dual_respects {L M : LineCore.{u} (B := B) IB}
    (h : Isomorphic IB L M) :
    Isomorphic IB (L.dual IB) (M.dual IB) := by
  letI := L.holomorphic
  letI := M.holomorphic
  obtain ⟨e⟩ := h
  exact ⟨e.dual⟩

/-- Dualization descends to genuine cover-invariant line-core classes. -/
def CoreClass.dual (a : CoreClass.{u} (B := B) IB) :
    CoreClass.{u} (B := B) IB :=
  Quotient.liftOn a
    (fun L => Quotient.mk _ (L.dual IB))
    (by
      intro L M h
      exact Quotient.sound (dual_respects IB h))

end
end QuaternionicSymmetry.HolomorphicLineCoreClasses
