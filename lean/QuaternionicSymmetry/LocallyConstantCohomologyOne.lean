import QuaternionicSymmetry.LocallyConstantCocycleGauge
import QuaternionicSymmetry.SheafCechCohomologyComparison
import QuaternionicSymmetry.SheafCechCoefficientCohomology
import QuaternionicSymmetry.SheafCechDerivedSurjectivity

/-! Actual derived H¹ of a constant discrete ring sheaf vanishes on a
simply connected, locally path-connected space. The proof passes through
actual cocycle coverings, their lifted sections and derived extension
classes; no cohomology comparison or vanishing source is assumed. -/

namespace QuaternionicSymmetry.LocallyConstantCohomologyOne

open CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
open AbelianSheafCohomology LocallyConstantRingSheaf SheafCechOneCocycle
open LocallyConstantCocycleCovering LocallyConstantCocycleGauge
open SheafCechCocycleComparison SheafCechCoefficientMap SheafCechExtension
open SheafCechCohomologyComparison SheafCechCoefficientCohomology
open SheafCechDerivedSurjectivity
noncomputable section

variable {B R : Type} {ι : Type} [TopologicalSpace B] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R]
  {U : ι → Opens B} (c : OneCocycle (sectionSheaf B R) U)

def comparisonOfGauge (a : ∀ i, C(U i, R))
    (ha : ∀ i j (x : B) (hi : x ∈ U i) (hj : x ∈ U j),
      scalar c i j x + a j ⟨x, hj⟩ = a i ⟨x, hi⟩) :
    Comparison c (mappedCocycle (0 : sectionSheaf B R ⟶ sectionSheaf B R) c) where
  value i _ W hi _ := TopCat.ofHom ((a i).comp
    ⟨fun x : W => ⟨x.1, hi x.2⟩, continuous_subtype_val.subtype_mk _⟩)
  naturality _ _ _ _ _ _ _ := rfl
  compatibility i j i' j' W hi hj ha' hb := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change (show R from (c.value i j W hi hj).hom x) + a j ⟨x.1, hj x.2⟩ =
      a i ⟨x.1, hi x.2⟩ + 0
    rw [add_zero, ← scalar_eq_value c i j W hi hj x]
    exact ha i j x.1 (hi x.2) (hj x.2)

theorem cohomologyClass_eq_zero [SimplyConnectedSpace B] [LocPathConnectedSpace B]
    [Nonempty B] (hcover : ∀ x : B, ∃ i, x ∈ U i) :
    cohomologyClass c hcover = 0 := by
  classical
  let indexAt : B → ι := fun x => (hcover x).choose
  have mem_at : ∀ x : B, x ∈ U (indexAt x) := fun x => (hcover x).choose_spec
  obtain ⟨a, ha⟩ := exists_gauge c indexAt mem_at
  rw [SheafCechCohomologyComparison.cohomologyClass_eq (comparisonOfGauge c a ha) hcover,
    cohomologyClass_mapped]
  simp

theorem sectionSheaf_cohomologyOne_subsingleton
    [SimplyConnectedSpace B] [LocPathConnectedSpace B] [Nonempty B] :
    Subsingleton (cohomology B (sectionSheaf B R) 1) := by
  have hzero : ∀ x : cohomology B (sectionSheaf B R) 1, x = 0 := by
    intro x
    obtain ⟨U, hcover, c, rfl⟩ := exists_cocycle_of_cohomologyClass (sectionSheaf B R) x
    exact cohomologyClass_eq_zero c hcover
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end
end QuaternionicSymmetry.LocallyConstantCohomologyOne
