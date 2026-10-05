import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeClassicalPoint
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenSpecializationTensor

/-! The actual standard-open tensor evaluation point projects to precisely
the chosen Laurent torus point and the chosen actual chart point. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProductEvaluationProjections

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeStandardOpenSpecializationTensor
open ComplexProjectiveActualConeStandardOpenCounit
open ComplexProjectiveActualConeLocalizedSchemeClassicalPoint
open ComplexProjectiveActualConeClassicalCarrierEvaluation
open ComplexProjectiveActualConeChartClassicalSpecialization
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem actualChartEvaluation_scalar
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (w : Fin d → ℂ) (hw : w ∈ chartLocus A i) (c : ℂ) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    actualChartEvaluation A hA hNonempty i w hw
      (algebraMap ℂ (HomogeneousLocalization.Away
        (quotientPiece A) (coordinateClass A i)) c) = c := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  change chartPointEval A i w hw
    (standardOpenAlgEquiv A hA hNonempty i
      (algebraMap ℂ _ c)) = c
  rw [(standardOpenAlgEquiv A hA hNonempty i).commutes]
  exact chartPointEval_scalar A i w hw c

theorem actualProductEvaluation_left
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (w : Fin d → ℂ)
    (hw : w ∈ chartLocus A i) (t : TorusCoordinateRing r) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    actualProductEvaluation A hA hNonempty i z w hw
      ((Algebra.TensorProduct.includeLeft :
        TorusCoordinateRing r →ₐ[ℂ]
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) t) =
      evalTorus z t := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  change actualChartEvaluation A hA hNonempty i w hw
    (specializeStandardOpen A hA hNonempty i z (t ⊗ₜ[ℂ] 1)) = _
  rw [specializeStandardOpen_tmul, mul_one]
  exact actualChartEvaluation_scalar A hA hNonempty i w hw (evalTorus z t)

theorem actualProductEvaluation_right
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (w : Fin d → ℂ)
    (hw : w ∈ chartLocus A i)
    (a : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    actualProductEvaluation A hA hNonempty i z w hw
      ((Algebra.TensorProduct.includeRight :
        HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →ₐ[ℂ]
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) a) =
      actualChartEvaluation A hA hNonempty i w hw a := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  change actualChartEvaluation A hA hNonempty i w hw
    (specializeStandardOpen A hA hNonempty i z (1 ⊗ₜ[ℂ] a)) = _
  rw [specializeStandardOpen_tmul]
  simp

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProductEvaluationProjections
