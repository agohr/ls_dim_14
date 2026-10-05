import QuaternionicSymmetry.SheafCechDerivedSurjectivity
import QuaternionicSymmetry.HolomorphicLineDerivedClass
import QuaternionicSymmetry.HolomorphicUnitCocycleCore

/-! Every genuine derived H¹ class of the holomorphic-unit sheaf is
realized by an actual holomorphic line-bundle core. Together with the
earlier arbitrary-bundle representation, this is the surjectivity half
of the geometric Picard/H¹ correspondence. Injectivity and tensor
additivity remain separate obligations. -/

namespace QuaternionicSymmetry.HolomorphicLineDerivedSurjectivity

open CategoryTheory TopologicalSpace
open AbelianSheafCohomology SheafCechOneCocycle SheafCechExtension
open SheafCechDerivedSurjectivity HolomorphicUnitSheaf HolomorphicLineUnitCocycle
open HolomorphicLineCoreClasses HolomorphicLineDerivedClass HolomorphicUnitCocycleCore
open scoped Manifold ContDiff
noncomputable section

private theorem cocycle_ext {B ι : Type} [TopologicalSpace B]
    {A : AbelianSheaves B} {U : ι → Opens B} (c d : OneCocycle A U)
    (h : ∀ i j V hi hj, c.value i j V hi hj = d.value i j V hi hj) : c = d := by
  cases c
  cases d
  congr 1
  funext i j V hi hj
  exact h i j V hi hj

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

theorem classMap_surjective : Function.Surjective (classMap (B := B) IB) := by
  intro x
  obtain ⟨U, hcover, c, hc⟩ := exists_cocycle_of_cohomologyClass (unitSheaf IB) x
  let indexAt : B → B := fun b => (hcover b).choose
  have mem_at : ∀ b : B, b ∈ U (indexAt b) := fun b => (hcover b).choose_spec
  let C := lineCore IB c indexAt mem_at
  let L : LineCore.{0} (B := B) IB := {
    Index := B
    core := C
    holomorphic := inferInstance }
  refine ⟨Quotient.mk _ L, ?_⟩
  have hC : unitCocycle IB C = c := by
    apply cocycle_ext
    intro i j V hi hj
    exact unitCocycle_lineCore_value IB c indexAt mem_at i j V hi hj
  change cohomologyClass (unitCocycle IB C) hcover = x
  rw [hC]
  exact hc

end
end QuaternionicSymmetry.HolomorphicLineDerivedSurjectivity
