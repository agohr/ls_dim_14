import QuaternionicSymmetry.HolomorphicExponentialSequence
import QuaternionicSymmetry.LocallyConstantIntegerSheafComparison

/-! The exponential short exact sequence with the literal constant
`ULift ℤ` sheaf used by Mathlib's sheaf cohomology. The comparison to
locally constant functions is canonical, not an additional hypothesis. -/

namespace QuaternionicSymmetry.HolomorphicConstantExponentialSequence

open CategoryTheory CategoryTheory.Limits TopologicalSpace Manifold
open HolomorphicUnitSheaf HolomorphicExponentialSheaf
open HolomorphicIntegerSheafInclusion HolomorphicExponentialSequence
open LocallyConstantIntegerSheaf LocallyConstantIntegerSheafComparison
open scoped Manifold ContDiff
noncomputable section

private def liftedIntegerIso : AddCommGrpCat.of (ULift.{0} ℤ) ≅ AddCommGrpCat.of ℤ where
  hom := AddCommGrpCat.ofHom {
    toFun := ULift.down
    map_zero' := rfl
    map_add' _ _ := rfl }
  inv := AddCommGrpCat.ofHom {
    toFun := ULift.up
    map_zero' := rfl
    map_add' _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

variable {B : Type} [TopologicalSpace B]

def constantIntegralSheafIso :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{0} ℤ)) ≅
    (integerSheaf B : Sheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat) :=
  (constantSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat).mapIso
    liftedIntegerIso ≪≫ constantIntegerSheafIso B

variable {H F : Type*} [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

def constantExponentialComplex :
    ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat) :=
  ShortComplex.mk (constantIntegralSheafIso.hom ≫ integerInclusion (B := B) IB)
    (exponential IB) (by rw [Category.assoc, integerInclusion_exponential, comp_zero])

def constantExponentialComplexIso :
    constantExponentialComplex (B := B) IB ≅ exponentialComplex (B := B) IB :=
  ShortComplex.isoMk constantIntegralSheafIso (Iso.refl _) (Iso.refl _)
    (by simp [constantExponentialComplex, exponentialComplex])
    (by simp [constantExponentialComplex, exponentialComplex])

/-- The actual exponential sequence with exactly the constant integral
coefficient object appearing in the existing sheaf cohomology API. -/
theorem constantExponentialComplex_shortExact :
    (constantExponentialComplex (B := B) IB).ShortExact :=
  ShortComplex.shortExact_of_iso (constantExponentialComplexIso IB).symm
    (exponentialComplex_shortExact IB)

end
end QuaternionicSymmetry.HolomorphicConstantExponentialSequence
