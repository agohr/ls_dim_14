import QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapIso
import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapComplexMaps

/-! The inverse actual basic-open overlap comparison has exactly the
canonical homogeneous-localization restriction on each affine chart. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjOverlap
open ComplexProjectiveActualConeBasicOpenOverlapIso
open ComplexProjectiveActualConeOverlapComplexMaps
open ComplexProjectiveActualConeAwayComplexAlgebra
noncomputable section

variable {d : ℕ}

theorem actualBasicOpenOverlapIso_inv_left_spec
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    (actualBasicOpenCoordinateOverlapIso A hA hNonempty i j).inv ≫
      pullback.fst _ _ ≫
      (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
        (coordinateClass_mem_degreeOne A i) (by omega)).hom =
    Spec.map (CommRingCat.ofHom
      (overlapRestrictionLeft A hA hNonempty i j).toRingHom) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  simp [actualBasicOpenCoordinateOverlapIso, actualProjCoordinateOverlapIso,
    overlapRestrictionLeft, Proj.pullbackAwayιIso_inv_fst, Category.assoc]

theorem actualBasicOpenOverlapIso_inv_right_spec
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    (actualBasicOpenCoordinateOverlapIso A hA hNonempty i j).inv ≫
      pullback.snd _ _ ≫
      (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A j)
        (coordinateClass_mem_degreeOne A j) (by omega)).hom =
    Spec.map (CommRingCat.ofHom
      (overlapRestrictionRight A hA hNonempty i j).toRingHom) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  simp [actualBasicOpenCoordinateOverlapIso, actualProjCoordinateOverlapIso,
    overlapRestrictionRight, Proj.pullbackAwayιIso_inv_snd, Category.assoc]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapRestriction
