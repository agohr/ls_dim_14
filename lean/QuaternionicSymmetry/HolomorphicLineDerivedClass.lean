import QuaternionicSymmetry.SheafCechCommonRefinement
import QuaternionicSymmetry.HolomorphicLineGaugeUnitComparison
import QuaternionicSymmetry.HolomorphicLineBundleClassExhaustion

/-! Genuine holomorphic line-bundle classes have a well-defined class in
Mathlib's derived H¹ of the actual holomorphic-unit sheaf. The construction
uses actual transition functions and is independent of all trivializing
cover and gauge choices. Bijectivity and tensor additivity remain separate
obligations; no Picard classification is assumed here. -/

namespace QuaternionicSymmetry.HolomorphicLineDerivedClass

open CategoryTheory TopologicalSpace
open HolomorphicUnitSheaf HolomorphicLineUnitCocycle HolomorphicLineGauge
open HolomorphicLineGaugeUnitComparison HolomorphicLineCoreClasses
open HolomorphicLineBundleIsomorphism HolomorphicLineBundleClassExhaustion
open SheafCechExtension SheafCechCommonRefinement AbelianSheafCohomology
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

def coreClass (L : LineCore.{0} (B := B) IB) :
    cohomology B (unitSheaf IB) 1 := by
  letI := L.holomorphic
  exact cohomologyClass (unitCocycle IB L.core)
    (fun x => ⟨L.core.indexAt x, chartOpen_covers L.core x⟩)

theorem coreClass_respects {L K : LineCore.{0} (B := B) IB}
    (h : Isomorphic IB L K) : coreClass IB L = coreClass IB K := by
  letI := L.holomorphic
  letI := K.holomorphic
  obtain ⟨e⟩ := h
  exact cohomologyClass_comparison (gaugeComparison IB e) _ _

/-- The map from actual holomorphic line-bundle isomorphism classes into
genuine derived H¹, independent of the selected cover. -/
def classMap : CoreClass.{0} (B := B) IB → cohomology B (unitSheaf IB) 1 :=
  Quotient.lift (coreClass IB) (fun _ _ h => coreClass_respects IB h)

theorem classMap_mk (L : LineCore.{0} (B := B) IB) :
    classMap IB (Quotient.mk _ L) = coreClass IB L := rfl

variable (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (Bundle.TotalSpace ℂ V)]
  [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ∞ ℂ V IB]

/-- The cohomology class of an arbitrary actual holomorphic line bundle,
not only of a manually supplied transition-function presentation. -/
def bundleDerivedClass : cohomology B (unitSheaf IB) 1 :=
  classMap IB (bundleClass IB V)

theorem bundleDerivedClass_eq_representation
    (R : HolomorphicLineBundleRepresentationIso.Representation IB V) :
    bundleDerivedClass IB V = coreClass IB R.line := by
  unfold bundleDerivedClass
  rw [← representation_class_eq_bundleClass IB V R]
  rfl

variable (W : B → Type*) [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (Bundle.TotalSpace ℂ W)]
  [FiberBundle ℂ W] [VectorBundle ℂ ℂ W] [ContMDiffVectorBundle ∞ ℂ W IB]

theorem bundleDerivedClass_eq_of_iso (e : BundleIso IB V W) :
    bundleDerivedClass IB V = bundleDerivedClass IB W :=
  congrArg (classMap IB) ((bundleClass_eq_iff_isomorphic IB V W).2 ⟨e⟩)

end
end QuaternionicSymmetry.HolomorphicLineDerivedClass
