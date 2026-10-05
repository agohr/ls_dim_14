import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionLeftNaturality
import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionRightNaturality

/-! The checked ring-level localization naturality gives literal commuting
diagrams of affine scheme morphisms on both sides of a pairwise overlap. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeNaturality

open AlgebraicGeometry CategoryTheory
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
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem left_scheme_naturality
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    Spec.map (CommRingCat.ofHom
        (overlapTensorRestrictionLeft (r := r) A hA hNonempty i j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (standardOpenCoaction μ A hA hNonempty hCompact i)) =
    Spec.map (CommRingCat.ofHom
        (localizedCoactionLeft μ A hA hNonempty hCompact i j)) ≫
      Spec.map (CommRingCat.ofHom
        (overlapRestrictionLeft A hA hNonempty i j).toRingHom) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  congr 1
  apply RingHom.ext
  intro a
  exact (localizedCoactionLeft_restrict μ A hA hNonempty hCompact i j a).symm

set_option maxRecDepth 2048 in
theorem right_scheme_naturality
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    Spec.map (CommRingCat.ofHom
        (overlapTensorRestrictionRight (r := r) A hA hNonempty i j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (standardOpenCoaction μ A hA hNonempty hCompact j)) =
    Spec.map (CommRingCat.ofHom
        (localizedCoactionRight μ A hA hNonempty hCompact i j)) ≫
      Spec.map (CommRingCat.ofHom
        (overlapRestrictionRight A hA hNonempty i j).toRingHom) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  congr 1
  apply RingHom.ext
  intro a
  exact (localizedCoactionRight_restrict μ A hA hNonempty hCompact i j a).symm

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeNaturality
