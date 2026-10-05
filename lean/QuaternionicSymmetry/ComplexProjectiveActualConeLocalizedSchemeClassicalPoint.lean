import QuaternionicSymmetry.ComplexProjectiveActualConeTensorClassicalPoint
import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedClassicalFunctions

/-! The genuine affine Scheme map induced by the actual standard-open
coaction sends its canonical complex evaluation point to the evaluation
point of the analytic diagonal chart transform. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeClassicalPoint

open AlgebraicGeometry ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalHolomorphic
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenCounit
open ComplexProjectiveActualConeLocalizedClassicalFunctions
open ComplexProjectiveActualConeSpecEvaluationNaturality
open ComplexProjectiveActualConeChartClassicalSpecialization
open ComplexProjectiveTorusPreservation
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def actualChartEvaluation
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (w : Fin d → ℂ) (hw : w ∈ chartLocus A i) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →+* ℂ := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  exact (chartPointEval A i w hw).comp
    (standardOpenAlgEquiv A hA hNonempty i).toRingHom

def actualProductEvaluation
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (w : Fin d → ℂ)
    (hw : w ∈ chartLocus A i) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    ((TorusCoordinateRing r) ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) →+* ℂ := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  exact (actualChartEvaluation A hA hNonempty i w hw).comp
    (specializeStandardOpen A hA hNonempty i z)

theorem actualProductEvaluation_action
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (z : ComplexTorus r)
    (w : Fin d → ℂ) (hw : w ∈ chartLocus A i) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    (actualProductEvaluation A hA hNonempty i z w hw).comp
      (standardOpenCoaction μ A hA hNonempty hCompact i) =
      actualChartEvaluation A hA hNonempty i
        (chartDiagonal μ z i w)
        (chartDiagonal_maps_chartLocus μ z A
          (mapsTo_of_compact μ A hA hCompact z) i hw) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  apply RingHom.ext
  intro a
  exact localized_classical_function_action μ A hA hNonempty hCompact i z w hw a

theorem actualLocalSpecAction_classical
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (z : ComplexTorus r)
    (w : Fin d → ℂ) (hw : w ∈ chartLocus A i) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    Spec.map (CommRingCat.ofHom
      (standardOpenCoaction μ A hA hNonempty hCompact i))
      (specEvaluationPoint (actualProductEvaluation A hA hNonempty i z w hw)) =
      specEvaluationPoint (actualChartEvaluation A hA hNonempty i
        (chartDiagonal μ z i w)
        (chartDiagonal_maps_chartLocus μ z A
          (mapsTo_of_compact μ A hA hCompact z) i hw)) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  rw [specMap_specEvaluationPoint]
  rw [actualProductEvaluation_action]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeClassicalPoint
