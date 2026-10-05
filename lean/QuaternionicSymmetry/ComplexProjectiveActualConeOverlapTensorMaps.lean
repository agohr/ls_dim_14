import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapComplexMaps

/-! Restriction of the literal torus-coordinate base changes to an actual
pairwise standard-open overlap. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeOverlapTensorMaps

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapComplexMaps
open ComplexProjectiveDiagonalAlgebraicCharts
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def overlapTensorRestrictionLeft (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    TorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →ₐ[TorusCoordinateRing r]
    TorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  exact Algebra.TensorProduct.map (AlgHom.id (TorusCoordinateRing r) (TorusCoordinateRing r))
    (overlapRestrictionLeft A hA hNonempty i j)

def overlapTensorRestrictionRight (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    TorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j) →ₐ[TorusCoordinateRing r]
    TorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A j)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  exact Algebra.TensorProduct.map (AlgHom.id (TorusCoordinateRing r) (TorusCoordinateRing r))
    (overlapRestrictionRight A hA hNonempty i j)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeOverlapTensorMaps
