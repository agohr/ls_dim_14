import QuaternionicSymmetry.SheafCechDerivedInjectivity
import QuaternionicSymmetry.HolomorphicLineDerivedSurjectivity
import QuaternionicSymmetry.HolomorphicLineUnitComparisonGauge

/-! Genuine holomorphic line-bundle isomorphism classes are in bijection
with Mathlib's actual derived H¹ of the holomorphic-unit sheaf. The map is
the previously constructed extension-class map. This proves the set-level
classification; compatibility with tensor multiplication is separate. -/

namespace QuaternionicSymmetry.HolomorphicLineDerivedEquivalence

open CategoryTheory TopologicalSpace
open AbelianSheafCohomology HolomorphicUnitSheaf HolomorphicLineUnitCocycle
open HolomorphicLineCoreClasses HolomorphicLineDerivedClass
open HolomorphicLineDerivedSurjectivity HolomorphicLineUnitComparisonGauge
open SheafCechDerivedInjectivity
open HolomorphicLineBundleIsomorphism HolomorphicLineBundleClassExhaustion
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

theorem coreClass_eq_iff_isomorphic (L K : LineCore.{0} (B := B) IB) :
    coreClass IB L = coreClass IB K ↔ Isomorphic IB L K := by
  letI := L.holomorphic
  letI := K.holomorphic
  exact (cohomologyClass_eq_iff_comparison (unitCocycle IB L.core) (unitCocycle IB K.core)
    (fun x => ⟨L.core.indexAt x, chartOpen_covers L.core x⟩)
    (fun x => ⟨K.core.indexAt x, chartOpen_covers K.core x⟩)).trans
      (nonempty_gauge_iff_cocycleComparison IB).symm

theorem classMap_injective : Function.Injective (classMap (B := B) IB) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro L K h
  exact Quotient.sound ((coreClass_eq_iff_isomorphic IB L K).mp h)

/-- The actual classifying map, now proved bijective, without replacing
derived cohomology by a newly defined cocycle quotient. -/
def classEquiv : CoreClass.{0} (B := B) IB ≃ cohomology B (unitSheaf IB) 1 :=
  Equiv.ofBijective (classMap IB) ⟨classMap_injective IB, classMap_surjective IB⟩

theorem classEquiv_apply (L : CoreClass.{0} (B := B) IB) :
    classEquiv IB L = classMap IB L := rfl

variable (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (Bundle.TotalSpace ℂ V)]
  [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ∞ ℂ V IB]
  (W : B → Type*) [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (Bundle.TotalSpace ℂ W)]
  [FiberBundle ℂ W] [VectorBundle ℂ ℂ W] [ContMDiffVectorBundle ∞ ℂ W IB]

theorem bundleDerivedClass_eq_iff_isomorphic :
    bundleDerivedClass IB V = bundleDerivedClass IB W ↔ Nonempty (BundleIso IB V W) := by
  change classMap IB (bundleClass IB V) = classMap IB (bundleClass IB W) ↔ _
  rw [(classMap_injective IB).eq_iff]
  exact bundleClass_eq_iff_isomorphic IB V W

end
end QuaternionicSymmetry.HolomorphicLineDerivedEquivalence
