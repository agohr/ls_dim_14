import QuaternionicSymmetry.ComplexProjectiveActualConeAllFractionTensorCoordinates
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenSpecializationTensor
import QuaternionicSymmetry.ComplexProjectiveActualConeChartClassicalSpecialization
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenAlgEquiv

/-! The actual homogeneous-localization coaction, specialized at a complex
torus point and evaluated in the matching classical chart, has the analytic
diagonal coordinate formula. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedClassicalAction

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalHolomorphic
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeAllFractionTensorCoordinates
open ComplexProjectiveActualConeStandardOpenSpecializationTensor
open ComplexProjectiveActualConeStandardOpenCounit
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeStandardOpenCoordinates
open ComplexProjectiveActualConeChartClassicalSpecialization
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem localized_classical_coordinate
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (k : Fin d)
    (z : ComplexTorus r) (w : Fin d → ℂ)
    (hw : w ∈ chartLocus A i) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    chartPointEval A i w hw
      (standardOpenAlgEquiv A hA hNonempty i
        (specializeStandardOpen A hA hNonempty i z
          (standardOpenCoaction μ A hA hNonempty hCompact i
            (coordinateFraction A hA hNonempty i (i.succAbove k))))) =
      chartDiagonal μ z i w k := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  rw [standardOpenCoaction_fraction_tensor,
    specializeStandardOpen_tmul]
  rw [map_mul]
  have hfrac : standardOpenAlgEquiv A hA hNonempty i
      (coordinateFraction A hA hNonempty i (i.succAbove k)) =
      Ideal.Quotient.mk (ComplexProjectiveDiagonalChartVanishingIdeal.chartVanishingIdeal A i)
        (MvPolynomial.X k) := by
    exact standardOpenToChart_coordinate A hA hNonempty i k
  rw [hfrac, map_mul (chartPointEval A i w hw)]
  rw [(standardOpenAlgEquiv A hA hNonempty i).commutes]
  rw [chartPointEval_mk]
  simp only [MvPolynomial.eval_X]
  have hs (c : ℂ) : chartPointEval A i w hw
      (algebraMap ℂ (MvPolynomial (Fin d) ℂ ⧸
        ComplexProjectiveDiagonalChartVanishingIdeal.chartVanishingIdeal A i) c) = c := by
    change chartPointEval A i w hw
      (Ideal.Quotient.mk _ (MvPolynomial.C c)) = c
    rw [chartPointEval_mk]
    simp
  rw [hs]
  simpa [regularChartCoordinate, evalTorus_laurentMonomial] using
    (eval_regularChartCoordinate μ i k z w)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedClassicalAction
