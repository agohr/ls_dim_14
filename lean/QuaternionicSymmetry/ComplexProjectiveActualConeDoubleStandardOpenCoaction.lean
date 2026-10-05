import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenRing
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoaction

/-! The checked two-torus chart quotient maps transported to genuine tensor
products with the actual homogeneous standard-open ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoaction

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalDoubleChartQuotientMaps
open ComplexProjectiveDiagonalDoubleChartQuotientCoaction
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeBaseChangedChartRing
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenRing
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def firstStandardOpenTwist
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (TorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) →+*
    (DoubleTorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm.toRingHom.comp
    ((firstChartTwistQuotient μ A hA hCompact i).comp
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).toRingHom)

def secondStandardOpenTwist
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (TorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) →+*
    (DoubleTorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm.toRingHom.comp
    ((secondChartTwistQuotient μ A hA hCompact i).comp
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).toRingHom)

def comultiplicationStandardOpen
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (TorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) →+*
    (DoubleTorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm.toRingHom.comp
    ((comultiplicationChartQuotient (r := r) A i).comp
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).toRingHom)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoaction
