import QuaternionicSymmetry.ComplexProjectiveActualConeProjCoordinateCover
import QuaternionicSymmetry.ComplexProjectiveActualConeChartStructureCompatibility
import Mathlib.AlgebraicGeometry.Gluing

/-! The literal torus × actual cone Proj has a finite scheme open cover
whose objects are the already constructed torus × coordinate basic opens. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoordinateCover

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjCoordinateCover
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveDiagonalAlgebraicCharts
noncomputable section

variable {r d : ℕ}

def actualConeCoordinateOpenCover (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    Scheme.OpenCover (Proj (quotientPiece A)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact (Proj (quotientPiece A)).openCoverOfIsOpenCover
    (fun i : Fin (d + 1) => Proj.basicOpen (quotientPiece A) (coordinateClass A i))
    (coordinate_basicOpens_cover A hA hNonempty)

def actualConeTorusProductCoordinateCover (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    Scheme.OpenCover
      (pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
        (actualConeProjToSpecComplex A hA hNonempty)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact Scheme.Pullback.openCoverOfRight
    (actualConeCoordinateOpenCover A hA hNonempty)
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
    (actualConeProjToSpecComplex A hA hNonempty)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoordinateCover
