import QuaternionicSymmetry.SheafCechCocycleAddition
import QuaternionicSymmetry.SheafCechCoefficientCohomology

/-! Addition of actual cocycle sections equals the canonical addition
in Mathlib's derived H¹, via the actual coefficient biproduct. -/

namespace QuaternionicSymmetry.SheafCechCohomologyAddition

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open AbelianSheafCohomology SheafCechOneCocycle SheafCechExtension
open SheafCechCoefficientMap SheafCechCoefficientCohomology SheafCechCocycleAddition
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A : AbelianSheaves B} {U : ι → Opens B}
  (c d : OneCocycle A U) (hcover : ∀ x : B, ∃ i, x ∈ U i)

theorem cohomologyClass_sum :
    cohomologyClass (sumCocycle c d) hcover =
      cohomologyClass c hcover + cohomologyClass d hcover := by
  calc
    _ = cohomologyClass (mappedCocycle (biprod.fst + biprod.snd) (pairedCocycle c d))
        hcover := by rw [mapped_pair_add]
    _ = (cohomologyClass (pairedCocycle c d) hcover).comp
        (Ext.mk₀ (biprod.fst + biprod.snd)) (add_zero 1) :=
      cohomologyClass_mapped _ _ hcover
    _ = (cohomologyClass (pairedCocycle c d) hcover).comp (Ext.mk₀ biprod.fst) (add_zero 1) +
        (cohomologyClass (pairedCocycle c d) hcover).comp (Ext.mk₀ biprod.snd) (add_zero 1) := by
      rw [Ext.mk₀_add, Ext.comp_add]
    _ = _ := by
      rw [← cohomologyClass_mapped, ← cohomologyClass_mapped,
        mapped_pair_fst, mapped_pair_snd]

end
end QuaternionicSymmetry.SheafCechCohomologyAddition
