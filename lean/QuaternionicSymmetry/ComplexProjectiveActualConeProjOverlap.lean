import QuaternionicSymmetry.ComplexProjectiveActualConeChartStructureCompatibility

/-! The pairwise intersections of the actual cone Proj coordinate charts
are literally Mathlib's homogeneous localizations at products of actual
coordinate classes. These are the comparison rings for gluing the local
regular torus maps. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjOverlap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
noncomputable section

variable {d : ℕ}

theorem coordinateProduct_mem_degreeTwo (A : Set (Space d))
    (i j : Fin (d + 1)) :
    coordinateClass A i * coordinateClass A j ∈ quotientPiece A 2 := by
  simpa using mul_mem_quotientPiece A
    (coordinateClass_mem_degreeOne A i)
    (coordinateClass_mem_degreeOne A j)

def actualProjCoordinateOverlapIso (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    pullback
      (Proj.awayι (quotientPiece A) (coordinateClass A i)
        (coordinateClass_mem_degreeOne A i) (by omega))
      (Proj.awayι (quotientPiece A) (coordinateClass A j)
        (coordinateClass_mem_degreeOne A j) (by omega)) ≅
      Spec (CommRingCat.of
        (HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i * coordinateClass A j))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact Proj.pullbackAwayιIso (quotientPiece A)
    (coordinateClass_mem_degreeOne A i) (by omega)
    (coordinateClass_mem_degreeOne A j) (by omega) rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjOverlap
