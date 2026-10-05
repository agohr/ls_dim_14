import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenAlgEquiv
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductScheme

/-! The actual Laurent family chart ring is the torus-coordinate base
change of the genuine homogeneous standard-open ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeBaseChangedChartRing

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveDiagonalChartProductScheme
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def baseChangedStandardOpenEquiv (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    (TorusCoordinateRing r) ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) ≃ₐ[TorusCoordinateRing r]
    (TorusCoordinateRing r) ⊗[ℂ]
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  exact Algebra.TensorProduct.congr (AlgEquiv.refl :
    TorusCoordinateRing r ≃ₐ[TorusCoordinateRing r] TorusCoordinateRing r)
    (standardOpenAlgEquiv A hA hNonempty i)

def baseChangedStandardOpenFamilyEquiv (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    (TorusCoordinateRing r) ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) ≃+*
    (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸
      extendedChartIdeal (r := r) A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  exact (baseChangedStandardOpenEquiv (r := r) A hA hNonempty i).toRingEquiv.trans
    (chartFamilyProductRingEquiv (r := r) A i).symm

end
end QuaternionicSymmetry.ComplexProjectiveActualConeBaseChangedChartRing
