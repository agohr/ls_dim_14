import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoordinateCover
import QuaternionicSymmetry.CategoryPullbackProductOverlapIso

/-! The actual product-coordinate open-cover maps agree with the generic
base-changed-open maps used by the categorical overlap comparison. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverMap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeProjProductCoordinateCover
open CategoryPullbackProductOverlapIso
open ComplexProjectiveDiagonalAlgebraicCharts
noncomputable section

variable {r d : ℕ}

theorem actualConeTorusProductCover_f_eq_baseChangedOpenMap
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    (actualConeTorusProductCoordinateCover (r := r) A hA hNonempty).f i =
      baseChangedOpenMap
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
        (actualConeProjToSpecComplex A hA hNonempty)
        (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  apply pullback.hom_ext
  · simp [actualConeTorusProductCoordinateCover, actualConeCoordinateOpenCover,
      baseChangedOpenMap]
  · simp [actualConeTorusProductCoordinateCover, actualConeCoordinateOpenCover,
      baseChangedOpenMap]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverMap
