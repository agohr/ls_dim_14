import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionRightNaturality
import QuaternionicSymmetry.ComplexProjectiveActualConeRestrictedCoactionCoordinates

/-! The two genuine localization lifts agree on every restricted projective
coordinate fraction, by the checked tensor transition relation. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionGeneratorAgreement

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeOverlapComplexMaps
open ComplexProjectiveActualConeOverlapTensorMaps
open ComplexProjectiveActualConeLocalizedCoactionLeft
open ComplexProjectiveActualConeLocalizedCoactionRight
open ComplexProjectiveActualConeLocalizedCoactionLeftNaturality
open ComplexProjectiveActualConeLocalizedCoactionRightNaturality
open ComplexProjectiveActualConeRestrictedCoactionCoordinates
open ComplexProjectiveActualConeLocalizedCoactionRight
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem localizedCoactions_agree_on_coordinateFraction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j k : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    localizedCoactionRight μ A hA hNonempty hCompact i j
      ((overlapRestrictionLeft A hA hNonempty i j)
        (coordinateFraction A hA hNonempty i k)) =
    localizedCoactionLeft μ A hA hNonempty hCompact i j
      ((overlapRestrictionLeft A hA hNonempty i j)
        (coordinateFraction A hA hNonempty i k)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty (coordinateClass A j)
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
  let ρᵢ := localizedCoactionLeft μ A hA hNonempty hCompact i j
  let ρⱼ := localizedCoactionRight μ A hA hNonempty hCompact i j
  let l (k : Fin (d + 1)) := (overlapRestrictionLeft A hA hNonempty i j)
    (coordinateFraction A hA hNonempty i k)
  let q (k : Fin (d + 1)) := (overlapRestrictionRight A hA hNonempty i j)
    (coordinateFraction A hA hNonempty j k)
  have htrans : l k * q i = q k :=
    overlap_coordinate_transition A hA hNonempty i j k
  have happly : ρⱼ (l k) * ρⱼ (q i) = ρⱼ (q k) := by
    simpa only [map_mul] using congrArg ρⱼ htrans
  have hright (m : Fin (d + 1)) :
      ρⱼ (q m) = overlapTensorRestrictionRight (r := r) A hA hNonempty i j
        (ComplexProjectiveActualConeStandardOpenCoaction.standardOpenCoaction
          μ A hA hNonempty hCompact j (coordinateFraction A hA hNonempty j m)) :=
    localizedCoactionRight_restrict μ A hA hNonempty hCompact i j _
  have hleft : ρᵢ (l k) = overlapTensorRestrictionLeft (r := r) A hA hNonempty i j
      (ComplexProjectiveActualConeStandardOpenCoaction.standardOpenCoaction
        μ A hA hNonempty hCompact i (coordinateFraction A hA hNonempty i k)) :=
    localizedCoactionLeft_restrict μ A hA hNonempty hCompact i j _
  have hu : IsUnit (ρⱼ (q i)) := by
    rw [hright]
    exact right_restricted_coaction_fraction_isUnit μ A hA hNonempty hCompact i j
  apply hu.mul_right_cancel
  calc
    ρⱼ (l k) * ρⱼ (q i) = ρⱼ (q k) := happly
    _ = ρᵢ (l k) * ρⱼ (q i) := by
      rw [hleft, hright i, hright k]
      exact (restricted_coaction_transition μ A hA hNonempty hCompact i j k).symm

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionGeneratorAgreement
