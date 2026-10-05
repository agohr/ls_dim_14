import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeAction
import QuaternionicSymmetry.ComplexProjectiveActualConeLocalActionOverComplex
import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverMap

/-! The glued genuine regular torus-family action is a morphism over the
canonical `Spec ℂ` structure, as witnessed on the actual product-coordinate
open cover. This permits the literal iterated product action to be formed. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeGlobalActionOverComplex

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProjProductCoverMap
open ComplexProjectiveActualConeGlobalSchemeAction
open ComplexProjectiveActualConeLocalActionOverComplex
open CategoryPullbackProductOverlapIso
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem globalSchemeAction_over_complex
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    globalSchemeAction μ A hA hNonempty hCompact ≫
      actualConeProjToSpecComplex A hA hNonempty =
    pullback.fst _ _ ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
  apply 𝒰.hom_ext
  intro i
  rw [← Category.assoc (𝒰.f i),
    globalSchemeAction_restrict μ A hA hNonempty hCompact i]
  rw [actualConeTorusProductCover_f_eq_baseChangedOpenMap
    (r := r) A hA hNonempty i]
  simpa [ComplexProjectiveActualConeProductCoverDirectAction.productCoverDirectLocalAction,
    baseChangedOpenMap, Category.assoc] using
    directBasicOpenProductAction_over_complex μ A hA hNonempty hCompact i

end
end QuaternionicSymmetry.ComplexProjectiveActualConeGlobalActionOverComplex
