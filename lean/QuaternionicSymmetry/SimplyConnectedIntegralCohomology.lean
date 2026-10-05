import QuaternionicSymmetry.LocallyConstantCohomologyOne
import QuaternionicSymmetry.IntegralCohomologyTorsion

/-! The actual integral sheaf-cohomology H² group is torsion-free on a
simply connected, locally path-connected nonempty space. The proof derives
the finite-coefficient H¹ vanishings internally from actual covering lifts.
It does not assert simple connectedness, finite generation or rank for the
twistor, which remain separate geometric/topological obligations. -/

namespace QuaternionicSymmetry.SimplyConnectedIntegralCohomology

open CategoryTheory CategoryTheory.Abelian TopologicalSpace
open AbelianSheafCohomology ConstantIntegralCoefficientSequence
open LocallyConstantRingSheaf LocallyConstantCohomologyOne
open IntegralCohomologyTorsion
noncomputable section

variable (B : Type) [TopologicalSpace B] [SimplyConnectedSpace B]
  [LocPathConnectedSpace B] [Nonempty B]

theorem constantRing_cohomologyOne_subsingleton (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R] :
    Subsingleton (cohomology B
      ((constantCoefficients B).obj (AddCommGrpCat.of R)) 1) := by
  letI := sectionSheaf_cohomologyOne_subsingleton (B := B) (R := R)
  let e : cohomology B ((constantCoefficients B).obj (AddCommGrpCat.of R)) 1 ≃+
      cohomology B (sectionSheaf B R) 1 :=
    ((extFunctorObj (integralSheaf B) 1).mapIso
      (constantRingSheafIso B R)).addCommGroupIsoToAddEquiv
  exact e.injective.subsingleton

theorem finiteCoefficient_cohomologyOne_subsingleton (k : ℕ) :
    Subsingleton (cohomology B (finiteCoefficientSheaf B k) 1) := by
  letI : TopologicalSpace (ZMod k) := ⊥
  letI : DiscreteTopology (ZMod k) := ⟨rfl⟩
  exact constantRing_cohomologyOne_subsingleton B (ZMod k)

/-- No additional cohomology-vanishing or torsion-freeness premise is used. -/
theorem integralCohomology_two_torsionFree :
    IsAddTorsionFree (cohomology B (integralSheaf B) 2) :=
  isAddTorsionFree_of_finiteCoefficient_vanishing B 1
    (fun k _ => finiteCoefficient_cohomologyOne_subsingleton B k)

end
end QuaternionicSymmetry.SimplyConnectedIntegralCohomology
