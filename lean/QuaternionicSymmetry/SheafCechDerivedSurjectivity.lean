import QuaternionicSymmetry.SheafExtensionReconstructionClass
import QuaternionicSymmetry.DerivedExtensionClassRealization

/-! Every actual derived H¹ class of an abelian sheaf on a topological
space is represented by a genuine Čech cocycle on an actual open cover.
This is proved by extension realization, local lifts, and reconstruction;
no Čech/derived comparison theorem is added as a literature premise. -/

namespace QuaternionicSymmetry.SheafCechDerivedSurjectivity

open CategoryTheory TopologicalSpace
open AbelianSheafCohomology SheafCechOneCocycle SheafCechExtension
open IntegralSheafLocalUnitLift SheafExtensionCocycle
open SheafExtensionReconstructionClass DerivedExtensionClassRealization
noncomputable section

variable {B : Type} [TopologicalSpace B] (A : AbelianSheaves B)

theorem exists_cocycle_of_cohomologyClass (x : cohomology B A 1) :
    ∃ (U : B → Opens B) (hcover : ∀ b : B, ∃ i, b ∈ U i)
      (c : OneCocycle A U), cohomologyClass c hcover = x := by
  obtain ⟨M, f, g, hfg, hS, hx⟩ := exists_shortExact_extClass x
  letI := hS.epi_g
  refine ⟨liftOpen g, liftOpen_cover g,
    cocycle f g hfg hS (localUnitLift g) (localUnitLift_image g), ?_⟩
  exact (reconstructed_cohomologyClass f g hfg hS
    (localUnitLift g) (localUnitLift_image g) (liftOpen_cover g)).trans hx

end
end QuaternionicSymmetry.SheafCechDerivedSurjectivity
