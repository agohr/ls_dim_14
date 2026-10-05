import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoefficient
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenIteratedCoaction

/-! The ordered two-parameter twists have exact ring-map projections:
on the torus coefficient they are the untouched parameter inclusion, and
on the geometric standard-open ring they are the actual coaction followed
by the acted-on parameter inclusion. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTwistRingNaturality

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenCoefficient
open ComplexProjectiveActualConeStandardOpenParameterTensor
open ComplexProjectiveActualConeStandardOpenIteratedCoaction
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem secondTwist_comp_includeLeft
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (secondStandardOpenTwist μ A hA hNonempty hCompact i).comp
      (Algebra.TensorProduct.includeLeftRingHom :
        TorusCoordinateRing r →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) =
    (Algebra.TensorProduct.includeLeftRingHom :
        DoubleTorusCoordinateRing r →+*
          DoubleTorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)).comp
      (firstParameter (r := r)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro t
  exact secondStandardOpenTwist_tmul_one μ A hA hNonempty hCompact i t

set_option maxRecDepth 2048 in
theorem secondTwist_comp_includeRight
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (secondStandardOpenTwist μ A hA hNonempty hCompact i).comp
      (Algebra.TensorProduct.includeRight.toRingHom :
        HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i) →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) =
    (secondParameterStandardOpen (r := r) A hA hNonempty i).comp
      (standardOpenCoaction μ A hA hNonempty hCompact i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro x
  exact secondStandardOpenTwist_coaction_coordinate μ A hA hNonempty hCompact i x

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTwistRingNaturality
