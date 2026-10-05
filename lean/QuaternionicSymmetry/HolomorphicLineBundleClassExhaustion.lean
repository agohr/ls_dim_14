import QuaternionicSymmetry.HolomorphicLineBundleIsomorphism

/-! Choice independence and exhaustion for holomorphic line-bundle
classes. Any genuine holomorphic core representation gives the same class,
and re-extracting a core from an existing bundle preserves its class. -/

namespace QuaternionicSymmetry.HolomorphicLineBundleClassExhaustion

open HolomorphicLineCoreClasses HolomorphicLineBundleCoreRepresentation
open HolomorphicLineBundleRepresentationIso HolomorphicLineBundleIsomorphism
open HolomorphicLineGaugeFromBundleIso HolomorphicLineGaugeToBundleIso Bundle
open scoped Manifold ContDiff
noncomputable section

universe u v
variable {B : Type u} {H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

theorem representation_class_eq_bundleClass
    (V : B → Type v) [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ∞ ℂ V IB]
    (R : Representation IB V) :
    (Quotient.mk _ R.line : CoreClass IB) = bundleClass IB V := by
  letI := R.line.holomorphic
  let S := bundleRepresentation IB V
  change (Quotient.mk _ R.line : CoreClass IB) = Quotient.mk _ S.line
  apply (class_eq_iff_totalIso R.line S.line).2
  exact ⟨{
    fiberEquiv := fun x => (R.fiberEquiv x).trans (S.fiberEquiv x).symm
    holomorphicForward := S.holomorphicBackward.comp R.holomorphicForward
    holomorphicBackward := R.holomorphicBackward.comp S.holomorphicForward }⟩

theorem bundleClass_of_core (L : LineCore.{u} (B := B) IB) :
    letI := L.holomorphic
    bundleClass IB L.core.Fiber = (Quotient.mk _ L : CoreClass IB) := by
  letI := L.holomorphic
  let R : Representation IB L.core.Fiber := {
    line := L
    fiberEquiv := fun x => LinearEquiv.refl ℂ (L.core.Fiber x)
    holomorphicForward := contMDiff_id
    holomorphicBackward := contMDiff_id }
  exact (representation_class_eq_bundleClass IB L.core.Fiber R).symm

/-- Every group class is realized by a genuine holomorphic line bundle,
and passing that bundle back through the canonical representation changes
nothing in the group. -/
theorem every_class_realized (c : CoreClass.{u} (B := B) IB) :
    ∃ L : LineCore.{u} (B := B) IB,
      letI := L.holomorphic
      bundleClass IB L.core.Fiber = c := by
  induction c using Quotient.inductionOn with
  | h L => exact ⟨L, bundleClass_of_core IB L⟩

end
end QuaternionicSymmetry.HolomorphicLineBundleClassExhaustion
