import QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapRestriction
import QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapStructure

/-! Both affine chart restrictions of the actual homogeneous overlap have the
same target map to the literal cone `Proj`. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedTargetRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjOverlap
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeBasicOpenOverlapIso
open ComplexProjectiveActualConeBasicOpenOverlapRestriction
open ComplexProjectiveActualConeBasicOpenOverlapStructure
open ComplexProjectiveActualConeOverlapComplexMaps
open CategoryPullbackProductOverlapIso
noncomputable section

variable {d : ℕ}

theorem left_restriction_toProj
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    Spec.map (CommRingCat.ofHom
        (overlapRestrictionLeft A hA hNonempty i j).toRingHom) ≫
      (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
        (coordinateClass_mem_degreeOne A i) (by omega)).inv ≫
      (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι =
    Proj.awayι (quotientPiece A) (coordinateClass A i * coordinateClass A j)
      (coordinateProduct_mem_degreeTwo A i j) (by omega) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  rw [← actualBasicOpenOverlapIso_inv_left_spec A hA hNonempty i j]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact actualBasicOpenOverlapIso_inv_toProj A hA hNonempty i j

theorem right_restriction_toProj
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    Spec.map (CommRingCat.ofHom
        (overlapRestrictionRight A hA hNonempty i j).toRingHom) ≫
      (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A j)
        (coordinateClass_mem_degreeOne A j) (by omega)).inv ≫
      (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι =
    Proj.awayι (quotientPiece A) (coordinateClass A i * coordinateClass A j)
      (coordinateProduct_mem_degreeTwo A i j) (by omega) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  rw [← actualBasicOpenOverlapIso_inv_right_spec A hA hNonempty i j]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [overlapToOriginal, pullback.condition, Category.assoc] using
    actualBasicOpenOverlapIso_inv_toProj A hA hNonempty i j

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedTargetRestriction
