import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionGeneratorAgreement
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoactionScalars

/-! The two actual localized overlap coactions agree on canonical global
complex scalars. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionScalars

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapComplexMaps
open ComplexProjectiveActualConeOverlapTensorMaps
open ComplexProjectiveActualConeLocalizedCoactionLeft
open ComplexProjectiveActualConeLocalizedCoactionRight
open ComplexProjectiveActualConeLocalizedCoactionLeftNaturality
open ComplexProjectiveActualConeLocalizedCoactionRightNaturality
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenCoactionScalars
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem localizedCoactions_agree_on_scalar
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) (c : ℂ) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    localizedCoactionLeft μ A hA hNonempty hCompact i j
      (algebraMap ℂ _ c) =
    localizedCoactionRight μ A hA hNonempty hCompact i j
      (algebraMap ℂ _ c) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty (coordinateClass A j)
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
  let xᵢ : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) :=
    algebraMap ℂ _ c
  let xⱼ : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j) :=
    algebraMap ℂ _ c
  have hi : (overlapRestrictionLeft A hA hNonempty i j) xᵢ =
      algebraMap ℂ _ c := (overlapRestrictionLeft A hA hNonempty i j).commutes c
  have hj : (overlapRestrictionRight A hA hNonempty i j) xⱼ =
      algebraMap ℂ _ c := (overlapRestrictionRight A hA hNonempty i j).commutes c
  calc
    localizedCoactionLeft μ A hA hNonempty hCompact i j (algebraMap ℂ _ c) =
        overlapTensorRestrictionLeft (r := r) A hA hNonempty i j
          (standardOpenCoaction μ A hA hNonempty hCompact i xᵢ) := by
            rw [← hi]
            exact localizedCoactionLeft_restrict μ A hA hNonempty hCompact i j xᵢ
    _ = (1 : TorusCoordinateRing r) ⊗ₜ[ℂ] (algebraMap ℂ _ c) := by
      rw [standardOpenCoaction_scalar]
      simp [overlapTensorRestrictionLeft, Algebra.TensorProduct.map_tmul]
    _ = overlapTensorRestrictionRight (r := r) A hA hNonempty i j
          (standardOpenCoaction μ A hA hNonempty hCompact j xⱼ) := by
      rw [standardOpenCoaction_scalar]
      simp [overlapTensorRestrictionRight, Algebra.TensorProduct.map_tmul]
    _ = localizedCoactionRight μ A hA hNonempty hCompact i j (algebraMap ℂ _ c) := by
      rw [← hj]
      exact (localizedCoactionRight_restrict μ A hA hNonempty hCompact i j xⱼ).symm

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionScalars
