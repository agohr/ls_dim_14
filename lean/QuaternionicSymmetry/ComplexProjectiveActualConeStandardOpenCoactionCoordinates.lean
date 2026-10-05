import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoaction
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoordinates

/-! Exact coordinate formula for the regular family after transport from
the actual homogeneous standard-open ring to the existing Laurent family
quotient. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoactionCoordinates

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalAffineChartComorphism
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeBaseChangedChartRing
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenCoordinates
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem standardOpenCoaction_coordinate
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (k : Fin d) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
      (standardOpenCoaction μ A hA hNonempty hCompact i
        (HomogeneousLocalization.Away.mk (quotientPiece A)
          (coordinateClass_mem_degreeOne A i) 1
          (coordinateClass A (i.succAbove k))
          (coordinateClass_mem_degreeOne A (i.succAbove k)))) =
      Ideal.Quotient.mk (extendedChartIdeal (r := r) A i)
        (regularChartCoordinate μ i k) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  simp only [standardOpenCoaction, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]
  rw [ComplexProjectiveActualConeStandardOpenEquiv.standardOpenEquiv_apply,
    standardOpenToChart_coordinate]
  simp [chartQuotientFamilyHom, chartActionComorphism_X]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoactionCoordinates
