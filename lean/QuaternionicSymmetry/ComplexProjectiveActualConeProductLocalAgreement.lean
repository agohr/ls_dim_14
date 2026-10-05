import QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapRestriction
import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedTargetRestriction
import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeNaturality
import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeAgreement
import QuaternionicSymmetry.ComplexProjectiveActualConeProductCoverDirectAction

/-! The actual local torus-family scheme maps agree after restriction to a
literal pairwise overlap of the product coordinate cover. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProductLocalAgreement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjOverlap
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProductOverlapAffineExplicit
open ComplexProjectiveActualConeProductOverlapRestriction
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeProductCoverDirectAction
open ComplexProjectiveActualConeLocalizedTargetRestriction
open ComplexProjectiveActualConeLocalizedSchemeNaturality
open ComplexProjectiveActualConeLocalizedSchemeAgreement
open ComplexProjectiveActualConeOverlapTensorMaps
open ComplexProjectiveActualConeLocalizedCoactionLeft
open ComplexProjectiveActualConeLocalizedCoactionRight
open ComplexProjectiveActualConeStandardOpenCoaction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem local_actions_agree_after_affine_overlap
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    let e := actualConeProductOverlapAffineIsoExplicit (r := r) A hA hNonempty i j
    e.inv ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫
      productCoverDirectLocalAction μ A hA hNonempty hCompact i =
    e.inv ≫ pullback.snd (𝒰.f i) (𝒰.f j) ≫
      productCoverDirectLocalAction μ A hA hNonempty hCompact j := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  let e := actualConeProductOverlapAffineIsoExplicit (r := r) A hA hNonempty i j
  let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
  have hL :
      (e.inv ≫ pullback.fst (𝒰.f i) (𝒰.f j)) ≫
        (directBasicOpenProductIso (r := r) A hA hNonempty i).hom =
      Spec.map (CommRingCat.ofHom
        (overlapTensorRestrictionLeft (r := r) A hA hNonempty i j).toRingHom) := by
    simpa only [Category.assoc] using
      actual_product_overlap_left_restriction (r := r) A hA hNonempty i j
  have hR :
      (e.inv ≫ pullback.snd (𝒰.f i) (𝒰.f j)) ≫
        (directBasicOpenProductIso (r := r) A hA hNonempty j).hom =
      Spec.map (CommRingCat.ofHom
        (overlapTensorRestrictionRight (r := r) A hA hNonempty i j).toRingHom) := by
    simpa only [Category.assoc] using
      actual_product_overlap_right_restriction (r := r) A hA hNonempty i j
  dsimp only [productCoverDirectLocalAction, directBasicOpenProductAction]
  simp only [← Category.assoc]
  rw [hL, hR]
  rw [left_scheme_naturality μ A hA hNonempty hCompact i j,
    right_scheme_naturality μ A hA hNonempty hCompact i j]
  rw [localized_scheme_actions_agree μ A hA hNonempty hCompact i j]
  simp only [Category.assoc]
  rw [left_restriction_toProj A hA hNonempty i j,
    right_restriction_toProj A hA hNonempty i j]

set_option maxHeartbeats 800000 in
theorem productCoverDirectLocalAction_agree
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    pullback.fst (𝒰.f i) (𝒰.f j) ≫
      productCoverDirectLocalAction μ A hA hNonempty hCompact i =
    pullback.snd (𝒰.f i) (𝒰.f j) ≫
      productCoverDirectLocalAction μ A hA hNonempty hCompact j := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let e := actualConeProductOverlapAffineIsoExplicit (r := r) A hA hNonempty i j
  let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
  have h := local_actions_agree_after_affine_overlap μ A hA hNonempty hCompact i j
  calc
    pullback.fst (𝒰.f i) (𝒰.f j) ≫
        productCoverDirectLocalAction μ A hA hNonempty hCompact i =
      e.hom ≫ e.inv ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫
        productCoverDirectLocalAction μ A hA hNonempty hCompact i := by
          simp only [Iso.hom_inv_id_assoc]
    _ = e.hom ≫ e.inv ≫ pullback.snd (𝒰.f i) (𝒰.f j) ≫
        productCoverDirectLocalAction μ A hA hNonempty hCompact j := by
          simpa only [Category.assoc] using congrArg (fun q => e.hom ≫ q) h
    _ = pullback.snd (𝒰.f i) (𝒰.f j) ≫
        productCoverDirectLocalAction μ A hA hNonempty hCompact j := by
          simp only [Iso.hom_inv_id_assoc]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProductLocalAgreement
