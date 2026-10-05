import QuaternionicSymmetry.SheafShortExactSections
import QuaternionicSymmetry.SheafCechTwistedPresheafSequence
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Topology.Sheaves.LocallySurjective

/-! The constant integral sheaf has a genuine canonical section 1 on
every open. Any epimorphism onto it admits lifts of 1 on an open cover,
by local surjectivity, without assuming surjectivity on global sections. -/

namespace QuaternionicSymmetry.IntegralSheafLocalUnitLift

open CategoryTheory TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle
open SheafCechTwistedPresheafSequence
noncomputable section

variable {B : Type} [TopologicalSpace B]

def unitSection (V : Opens B) : (integralSheaf B).val.obj (op V) :=
  (toSheafify (Opens.grothendieckTopology (TopCat.of B))
    (constantIntegerPresheaf (B := B))).app (op V) (ULift.up 1)

theorem unitSection_restrict {V W : Opens B} (hWV : W ≤ V) :
    restrict (integralSheaf B) hWV (unitSection V) = unitSection W := by
  exact (congrArg (fun k => k (ULift.up 1))
    ((toSheafify (Opens.grothendieckTopology (TopCat.of B))
      (constantIntegerPresheaf (B := B))).naturality (homOfLE hWV).op)).symm

variable {M : AbelianSheaves B} (g : M ⟶ integralSheaf B) [Epi g]

theorem exists_local_unit_lift (x : B) :
    ∃ (V : Opens B), x ∈ V ∧ ∃ s : M.val.obj (op V),
      g.val.app (op V) s = unitSection V := by
  have hlocal : Sheaf.IsLocallySurjective g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat g).mpr inferInstance
  obtain ⟨V, i, ⟨s, hs⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff g.val).mp hlocal
      ⊤ (unitSection ⊤) x (by trivial)
  refine ⟨V, hxV, s, ?_⟩
  exact hs.trans (unitSection_restrict i.le)

def liftOpen (x : B) : Opens B := (exists_local_unit_lift g x).choose

theorem mem_liftOpen (x : B) : x ∈ liftOpen g x :=
  (exists_local_unit_lift g x).choose_spec.1

def localUnitLift (x : B) : M.val.obj (op (liftOpen g x)) :=
  (exists_local_unit_lift g x).choose_spec.2.choose

@[simp] theorem localUnitLift_image (x : B) :
    g.val.app (op (liftOpen g x)) (localUnitLift g x) =
      unitSection (liftOpen g x) :=
  (exists_local_unit_lift g x).choose_spec.2.choose_spec

theorem liftOpen_cover : ∀ x : B, ∃ i, x ∈ liftOpen g i :=
  fun x => ⟨x, mem_liftOpen g x⟩

end
end QuaternionicSymmetry.IntegralSheafLocalUnitLift
