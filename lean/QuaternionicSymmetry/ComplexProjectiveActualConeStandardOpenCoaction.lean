import QuaternionicSymmetry.ComplexProjectiveActualConeBaseChangedChartRing
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamily

/-! The existing regular Laurent chart family, transported to the actual
homogeneous-localization standard-open ring and its true torus base change. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoaction

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeBaseChangedChartRing
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def standardOpenCoaction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →+*
      ((TorusCoordinateRing r) ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  exact (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm.toRingHom.comp
    ((chartQuotientFamilyHom μ A hA hCompact i).comp
      (standardOpenEquiv A hA hNonempty i).toRingHom)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoaction
