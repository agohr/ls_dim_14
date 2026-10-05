import QuaternionicSymmetry.ComplexProjectiveActualConeProductEvaluationProjections
import Mathlib.AlgebraicGeometry.Pullbacks

/-! The complex evaluation point of the actual torus/chart tensor ring is
the categorical fiber-product point with the prescribed torus and chart
components. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProductClassicalPoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeLocalizedSchemeClassicalPoint
open ComplexProjectiveActualConeProductEvaluationProjections
open ComplexProjectiveActualConeSpecEvaluationNaturality
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def actualClassicalProductPoint
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (w : Fin d → ℂ)
    (hw : w ∈ chartLocus A i) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    ↥(pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (HomogeneousLocalization.Away
          (quotientPiece A) (coordinateClass A i))))) : Scheme) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  exact (pullbackSpecIso ℂ (TorusCoordinateRing r)
    (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))).inv
      (specEvaluationPoint (actualProductEvaluation A hA hNonempty i z w hw))

theorem actualClassicalProductPoint_fst
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (w : Fin d → ℂ)
    (hw : w ∈ chartLocus A i) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    (pullback.fst _ _ : _ ⟶ Spec (CommRingCat.of (TorusCoordinateRing r)))
      (actualClassicalProductPoint A hA hNonempty i z w hw) =
      specEvaluationPoint (evalTorus z) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  change ((pullbackSpecIso ℂ (TorusCoordinateRing r)
    (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))).inv ≫
    pullback.fst _ _)
      (specEvaluationPoint (actualProductEvaluation A hA hNonempty i z w hw)) = _
  rw [pullbackSpecIso_inv_fst, specMap_specEvaluationPoint]
  congr 1
  apply RingHom.ext
  intro t
  exact actualProductEvaluation_left A hA hNonempty i z w hw t

theorem actualClassicalProductPoint_snd
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (w : Fin d → ℂ)
    (hw : w ∈ chartLocus A i) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    (pullback.snd _ _ : _ ⟶ Spec (CommRingCat.of
      (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))))
      (actualClassicalProductPoint A hA hNonempty i z w hw) =
      specEvaluationPoint (actualChartEvaluation A hA hNonempty i w hw) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  change ((pullbackSpecIso ℂ (TorusCoordinateRing r)
    (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))).inv ≫
    pullback.snd _ _)
      (specEvaluationPoint (actualProductEvaluation A hA hNonempty i z w hw)) = _
  rw [pullbackSpecIso_inv_snd, specMap_specEvaluationPoint]
  congr 1
  apply RingHom.ext
  intro a
  exact actualProductEvaluation_right A hA hNonempty i z w hw a

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProductClassicalPoint
