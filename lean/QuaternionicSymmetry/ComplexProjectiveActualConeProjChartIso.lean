import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenEquiv

/-! Each literal coordinate basic open of the actual cone Proj is the
literal affine `Spec` of the corresponding actual chart-locus quotient. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjChartIso

open AlgebraicGeometry
open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeStandardOpenEquiv
noncomputable section

variable {d : ℕ}

def actualProjChartIso (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).toScheme ≅
      Spec (CommRingCat.of
        (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)).trans
    (Scheme.Spec.mapIso (standardOpenEquiv A hA hNonempty i).symm.toCommRingCatIso.op)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjChartIso
