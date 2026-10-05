import QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapAffineExplicit
import QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapTensorRestriction
import QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapTensorRestrictionRight
import QuaternionicSymmetry.ComplexProjectiveActualConeDirectLocalSchemeAction

/-! Literal restriction maps of the actual finite product-cover objects,
under the explicit affine overlap iso, are the checked tensor localization
scheme morphisms. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProductOverlapAffineExplicit
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeOverlapTensorMaps
open ComplexProjectiveActualConeProductOverlapTensorRestriction
open ComplexProjectiveActualConeProductOverlapTensorRestrictionRight
open ComplexProjectiveDiagonalAlgebraicCharts
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem actual_product_overlap_left_restriction
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    (actualConeProductOverlapAffineIsoExplicit (r := r) A hA hNonempty i j).inv ≫
      pullback.fst (𝒰.f i) (𝒰.f j) ≫
      (directBasicOpenProductIso (r := r) A hA hNonempty i).hom =
    Spec.map (CommRingCat.ofHom
      (overlapTensorRestrictionLeft (r := r) A hA hNonempty i j).toRingHom) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  simpa only [actualConeProductOverlapAffineIsoExplicit, directBasicOpenProductIso,
    ComplexProjectiveActualConeProjProductCoordinateCover.actualConeTorusProductCoordinateCover,
    ComplexProjectiveActualConeProjProductCoordinateCover.actualConeCoordinateOpenCover,
    Iso.trans_inv, Iso.trans_hom, Category.assoc] using
    actual_left_tensor_restriction_staged (r := r) A hA hNonempty i j

theorem actual_product_overlap_right_restriction
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    (actualConeProductOverlapAffineIsoExplicit (r := r) A hA hNonempty i j).inv ≫
      pullback.snd (𝒰.f i) (𝒰.f j) ≫
      (directBasicOpenProductIso (r := r) A hA hNonempty j).hom =
    Spec.map (CommRingCat.ofHom
      (overlapTensorRestrictionRight (r := r) A hA hNonempty i j).toRingHom) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  simpa only [actualConeProductOverlapAffineIsoExplicit, directBasicOpenProductIso,
    ComplexProjectiveActualConeProjProductCoordinateCover.actualConeTorusProductCoordinateCover,
    ComplexProjectiveActualConeProjProductCoordinateCover.actualConeCoordinateOpenCover,
    Iso.trans_inv, Iso.trans_hom, Category.assoc] using
    actual_right_tensor_restriction_staged (r := r) A hA hNonempty i j

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapRestriction
