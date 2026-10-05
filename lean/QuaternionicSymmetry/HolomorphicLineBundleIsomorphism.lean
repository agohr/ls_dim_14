import QuaternionicSymmetry.HolomorphicLineBundleRepresentationIso
import QuaternionicSymmetry.HolomorphicLineGaugeToBundleIso

/-! The represented line-class group classifies genuine holomorphic
complex line bundles up to actual holomorphic fiberwise-linear total-space
isomorphism. The remaining analytic Picard bridge is to invertible sheaves
and cohomology, not representability of line bundles. -/

namespace QuaternionicSymmetry.HolomorphicLineBundleIsomorphism

open HolomorphicLineCoreClasses HolomorphicLineBundleCoreRepresentation
open HolomorphicLineBundleRepresentationIso HolomorphicLineGaugeFromBundleIso
open HolomorphicLineGaugeToBundleIso Bundle
open scoped Manifold ContDiff
noncomputable section

universe u v w
variable {B : Type u} {H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (V : B → Type v) [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
  [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ∞ ℂ V IB]

/-- The canonical represented class of a genuine holomorphic line bundle. -/
def bundleClass : CoreClass.{u} (B := B) IB :=
  Quotient.mk _ (representedLine IB V)

variable (W : B → Type w) [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace ℂ W)]
  [FiberBundle ℂ W] [VectorBundle ℂ ℂ W] [ContMDiffVectorBundle ∞ ℂ W IB]

/-- A genuine isomorphism of arbitrary actual holomorphic line bundles,
covering the identity on their common base. -/
structure BundleIso where
  fiberEquiv : ∀ x : B, V x ≃ₗ[ℂ] W x
  holomorphicForward : ContMDiff (IB.prod 𝓘(ℂ,ℂ)) (IB.prod 𝓘(ℂ,ℂ)) ∞
    (fun t : TotalSpace ℂ V => (⟨t.1, fiberEquiv t.1 t.2⟩ : TotalSpace ℂ W))
  holomorphicBackward : ContMDiff (IB.prod 𝓘(ℂ,ℂ)) (IB.prod 𝓘(ℂ,ℂ)) ∞
    (fun t : TotalSpace ℂ W => (⟨t.1, (fiberEquiv t.1).symm t.2⟩ : TotalSpace ℂ V))

/-- An isomorphism of the original bundles gives an isomorphism of their
represented cores by the already proved holomorphic representation maps. -/
def BundleIso.toCoreIso (e : BundleIso IB V W) :
    TotalIso (IB := IB) (bundleCore V) (bundleCore W) where
  fiberEquiv x := ((representationFiberEquiv V x).trans (e.fiberEquiv x)).trans
    (representationFiberEquiv W x).symm
  holomorphicForward :=
    (representationInverseTotalMap_holomorphic IB W).comp
      (e.holomorphicForward.comp (representationTotalMap_holomorphic IB V))
  holomorphicBackward :=
    (representationInverseTotalMap_holomorphic IB V).comp
      (e.holomorphicBackward.comp (representationTotalMap_holomorphic IB W))

/-- Conversely, an isomorphism between the represented cores realizes an
isomorphism between the original holomorphic line bundles. -/
def ofCoreIso (e : TotalIso (IB := IB) (bundleCore V) (bundleCore W)) :
    BundleIso IB V W where
  fiberEquiv x := (((representationFiberEquiv V x).symm).trans
    (e.fiberEquiv x)).trans (representationFiberEquiv W x)
  holomorphicForward :=
    (representationTotalMap_holomorphic IB W).comp
      (e.holomorphicForward.comp (representationInverseTotalMap_holomorphic IB V))
  holomorphicBackward :=
    (representationTotalMap_holomorphic IB V).comp
      (e.holomorphicBackward.comp (representationInverseTotalMap_holomorphic IB W))

/-- Equality of represented classes is neither weaker nor stronger than
actual holomorphic line-bundle isomorphism, even for unrelated fiber types. -/
theorem bundleClass_eq_iff_isomorphic :
    bundleClass IB V = bundleClass IB W ↔ Nonempty (BundleIso IB V W) := by
  rw [bundleClass, bundleClass, class_eq_iff_totalIso]
  constructor
  · rintro ⟨e⟩
    exact ⟨ofCoreIso IB V W e⟩
  · rintro ⟨e⟩
    exact ⟨e.toCoreIso⟩

end
end QuaternionicSymmetry.HolomorphicLineBundleIsomorphism
