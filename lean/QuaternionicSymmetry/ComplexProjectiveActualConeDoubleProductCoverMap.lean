import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductCover
import QuaternionicSymmetry.CategoryPullbackProductOverlapIso

/-! The actual double-torus product coordinate cover uses the canonical
base-changed basic-open maps, so its projections can be compared directly
with the local affine multiplication morphism. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductCoverMap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeDoubleProductCover
open CategoryPullbackProductOverlapIso
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

theorem actualConeDoubleTorusProductCover_f_eq_baseChangedOpenMap
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    (actualConeDoubleTorusProductCoordinateCover (r := r) A hA hNonempty).f i =
      baseChangedOpenMap
        (Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (DoubleTorusCoordinateRing r))))
        (actualConeProjToSpecComplex A hA hNonempty)
        (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  apply pullback.hom_ext
  · simp [actualConeDoubleTorusProductCoordinateCover, actualConeCoordinateOpenCover,
      baseChangedOpenMap]
  · simp [actualConeDoubleTorusProductCoordinateCover, actualConeCoordinateOpenCover,
      baseChangedOpenMap]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductCoverMap
