import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenParameterTensorMap
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalMultiplicationScheme
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductIteratedAction

/-! The actual affine basic-open map that forgets the first torus parameter
and retains the second parameter with the same geometric coordinate. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalSecondFactor

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDirectProductIsoProjection
open ComplexProjectiveActualConeDoubleProductLocalAction
open ComplexProjectiveActualConeDoubleProductIsoProjection
open ComplexProjectiveActualConeStandardOpenParameterTensor
open ComplexProjectiveActualConeStandardOpenParameterTensorMap
open ComplexProjectiveActualConeDoubleProductIteratedAction
open ComplexTorusLaurentComultiplication
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def directBasicOpenDoubleSecondFactor
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    pullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (DoubleTorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) ⟶
    pullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (TorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (directBasicOpenDoubleProductIso (r := r) A hA hNonempty i).hom ≫
    Spec.map (CommRingCat.ofHom
      (secondParameterStandardOpen (r := r) A hA hNonempty i)) ≫
    (directBasicOpenProductIso (r := r) A hA hNonempty i).inv

set_option maxRecDepth 2048 in
theorem secondParameterStandardOpen_comp_includeLeft
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (secondParameterStandardOpen (r := r) A hA hNonempty i).comp
      (Algebra.TensorProduct.includeLeftRingHom :
        TorusCoordinateRing r →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) =
    (Algebra.TensorProduct.includeLeftRingHom :
        DoubleTorusCoordinateRing r →+*
          DoubleTorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)).comp
      (secondParameter (r := r)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro t
  exact secondParameterStandardOpen_tmul A hA hNonempty i t 1

set_option maxRecDepth 2048 in
theorem secondParameterStandardOpen_comp_includeRight
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (secondParameterStandardOpen (r := r) A hA hNonempty i).comp
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
  simpa using secondParameterStandardOpen_tmul A hA hNonempty i 1 x

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalSecondFactor
