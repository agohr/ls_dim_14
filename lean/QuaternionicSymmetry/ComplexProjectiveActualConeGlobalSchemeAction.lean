import QuaternionicSymmetry.ComplexProjectiveActualConeProductLocalAgreement
import Mathlib.AlgebraicGeometry.Gluing

/-! The homogeneous diagonal coaction gives a genuine global regular scheme
morphism from the literal complex torus-product with the actual cone `Proj`.
Its restriction to each member of the actual finite product-coordinate cover
is exactly the checked affine action. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProductCoverDirectAction
open ComplexProjectiveActualConeProductLocalAgreement
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def globalSchemeAction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      (ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
        A hA hNonempty) ⟶ Proj (quotientPiece A) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
  exact 𝒰.glueMorphisms
    (productCoverDirectLocalAction μ A hA hNonempty hCompact)
    (productCoverDirectLocalAction_agree μ A hA hNonempty hCompact)

theorem globalSchemeAction_restrict
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    𝒰.f i ≫ globalSchemeAction μ A hA hNonempty hCompact =
      productCoverDirectLocalAction μ A hA hNonempty hCompact i := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
  exact 𝒰.ι_glueMorphisms
    (productCoverDirectLocalAction μ A hA hNonempty hCompact)
    (productCoverDirectLocalAction_agree μ A hA hNonempty hCompact) i

end
end QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeAction
