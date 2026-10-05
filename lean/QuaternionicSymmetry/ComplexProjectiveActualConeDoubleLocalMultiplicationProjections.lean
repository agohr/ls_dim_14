import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalMultiplication
import QuaternionicSymmetry.ComplexProjectiveActualConeDirectProductIsoProjection
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductIsoProjection

/-! The transported local multiplication has precisely the two expected
Scheme projections: Laurent multiplication on the torus factor and identity
on the actual standard-open geometric factor. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalMultiplicationProjections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenCoaction
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDirectProductIsoProjection
open ComplexProjectiveActualConeDoubleProductLocalAction
open ComplexProjectiveActualConeDoubleProductIsoProjection
open ComplexProjectiveActualConeDoubleLocalMultiplication
open ComplexProjectiveActualConeStandardOpenComultiplicationTensor
open ComplexProjectiveActualConeDoubleProductMultiplication
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem comultiplicationStandardOpen_comp_includeLeft
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (comultiplicationStandardOpen (r := r) A hA hNonempty i).comp
      (Algebra.TensorProduct.includeLeftRingHom :
        TorusCoordinateRing r →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) =
    (Algebra.TensorProduct.includeLeftRingHom :
        DoubleTorusCoordinateRing r →+*
          DoubleTorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)).comp
      (comultiplication (r := r)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro t
  exact comultiplicationStandardOpen_tmul A hA hNonempty i t 1

set_option maxRecDepth 2048 in
theorem comultiplicationStandardOpen_comp_includeRight
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (comultiplicationStandardOpen (r := r) A hA hNonempty i).comp
      (Algebra.TensorProduct.includeRight.toRingHom :
        HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i) →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) =
    (Algebra.TensorProduct.includeRight.toRingHom :
        HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i) →+*
          DoubleTorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro x
  simpa using comultiplicationStandardOpen_tmul A hA hNonempty i 1 x

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalMultiplicationProjections
