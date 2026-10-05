import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoordinateCover
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenRing
import Mathlib.AlgebraicGeometry.Gluing

/-! The genuine two-parameter torus scheme product with the actual cone
Proj has the coordinate basic-open cover. This is the source cover for the
global multiplication law. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductCover

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

def actualConeDoubleTorusProductCoordinateCover
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    Scheme.OpenCover
      (pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (DoubleTorusCoordinateRing r))))
        (actualConeProjToSpecComplex A hA hNonempty)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact Scheme.Pullback.openCoverOfRight
    (actualConeCoordinateOpenCover A hA hNonempty)
    (Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (DoubleTorusCoordinateRing r))))
    (actualConeProjToSpecComplex A hA hNonempty)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductCover
