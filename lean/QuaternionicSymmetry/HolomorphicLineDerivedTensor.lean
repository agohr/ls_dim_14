import QuaternionicSymmetry.HolomorphicLineDerivedEquivalence
import QuaternionicSymmetry.SheafCechCohomologyAddition
import QuaternionicSymmetry.HolomorphicLineCoreClassGroup

/-! The genuine line-bundle tensor operation corresponds to the canonical
addition on actual derived H¹. Thus the classifying bijection is a group
equivalence, not just a set-level correspondence. -/

namespace QuaternionicSymmetry.HolomorphicLineDerivedTensor

open CategoryTheory TopologicalSpace
open AbelianSheafCohomology HolomorphicUnitSheaf HolomorphicLineUnitCocycle
open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicLineDerivedClass HolomorphicLineDerivedEquivalence
open SheafCechOneCocycle SheafCechExtension SheafCechRefinement SheafCechCommonRefinement
open SheafCechCohomologyRefinement SheafCechCocycleAddition SheafCechCohomologyAddition
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

theorem unitCocycle_tensor {ι κ : Type}
    (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] :
    unitCocycle IB (HolomorphicLineTensor.tensorCore Z W) =
      sumCocycle
        (refinedCocycle (unitCocycle IB Z) (V := commonCover (chartOpen Z) (chartOpen W))
          Prod.fst (fun _ => inf_le_left))
        (refinedCocycle (unitCocycle IB W) (V := commonCover (chartOpen Z) (chartOpen W))
          Prod.snd (fun _ => inf_le_right)) := by
  apply cocycle_ext
  intro i j V hi hj
  apply Units.ext
  apply Subtype.ext
  funext x
  exact HolomorphicLineTensor.tensorCore_transitionScalar Z W i j x.1

theorem coreClass_tensor (L K : LineCore.{0} (B := B) IB) :
    coreClass IB (L.tensor IB K) = coreClass IB L + coreClass IB K := by
  letI := L.holomorphic
  letI := K.holomorphic
  let hL : ∀ x : B, ∃ i, x ∈ chartOpen L.core i :=
    fun x => ⟨L.core.indexAt x, chartOpen_covers L.core x⟩
  let hK : ∀ x : B, ∃ i, x ∈ chartOpen K.core i :=
    fun x => ⟨K.core.indexAt x, chartOpen_covers K.core x⟩
  let hLK := commonCover_covers hL hK
  change cohomologyClass (unitCocycle IB (HolomorphicLineTensor.tensorCore L.core K.core)) hLK =
    cohomologyClass (unitCocycle IB L.core) hL + cohomologyClass (unitCocycle IB K.core) hK
  rw [unitCocycle_tensor, cohomologyClass_sum]
  rw [← cohomologyClass_refinement (unitCocycle IB L.core) Prod.fst
    (fun _ => inf_le_left) hL hLK]
  rw [← cohomologyClass_refinement (unitCocycle IB K.core) Prod.snd
    (fun _ => inf_le_right) hK hLK]

theorem classMap_mul (a b : CoreClass.{0} (B := B) IB) :
    classMap IB (a * b) = classMap IB a + classMap IB b := by
  refine Quotient.inductionOn₂ a b ?_
  intro L K
  exact coreClass_tensor IB L K

/-- The class-group operation is the actual tensor operation already
constructed on bundles. `Additive` changes notation, not the group law. -/
def classAddEquiv : Additive (CoreClass.{0} (B := B) IB) ≃+
    cohomology B (unitSheaf IB) 1 where
  toEquiv := (show Additive (CoreClass.{0} (B := B) IB) ≃ CoreClass IB from
      { toFun := Additive.toMul
        invFun := Additive.ofMul
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }).trans (classEquiv IB)
  map_add' a b := classMap_mul IB a.toMul b.toMul

theorem classAddEquiv_apply (a : CoreClass.{0} (B := B) IB) :
    classAddEquiv IB (Additive.ofMul a) = classMap IB a := rfl

end
end QuaternionicSymmetry.HolomorphicLineDerivedTensor
