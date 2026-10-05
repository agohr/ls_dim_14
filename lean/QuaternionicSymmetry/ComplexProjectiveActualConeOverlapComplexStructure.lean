import QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapStructure
import QuaternionicSymmetry.ComplexProjectiveActualConeAwayComplexAlgebra
import QuaternionicSymmetry.ComplexProjectiveActualConeComplexStructure

/-! The affine pairwise overlap has the canonical complex structure induced
from the one global map on the actual cone `Proj`. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeOverlapComplexStructure

open AlgebraicGeometry CategoryTheory
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjOverlap
open ComplexProjectiveActualConeBasicOpenOverlapIso
open ComplexProjectiveActualConeBasicOpenOverlapStructure
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeDegreeZeroScalars
open QuaternionicSymmetry.CategoryPullbackProductOverlapIso
noncomputable section

variable {d : ℕ}

theorem actualBasicOpenOverlap_complexStructure
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) :=
        awayComplexAlgebra A hA hNonempty _
    (actualBasicOpenCoordinateOverlapIso A hA hNonempty i j).inv ≫
      overlapToOriginal
        (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
        (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι ≫
      actualConeProjToSpecComplex A hA hNonempty =
    Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j)))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty _
  rw [← Category.assoc, actualBasicOpenOverlapIso_inv_toProj]
  simp only [actualConeProjToSpecComplex]
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeOverlapComplexStructure
