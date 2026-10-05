import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeAction

/-! The global regular torus-family map is determined by its checked
standard-open restrictions. This is the extensionality interface for the
future unit and multiplication laws. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeActionUniqueness

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProductCoverDirectAction
open ComplexProjectiveActualConeGlobalSchemeAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem globalSchemeAction_unique
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (φ :
      letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
        (ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
          A hA hNonempty) ⟶ Proj (quotientPiece A))
    (hφ :
      letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
      let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
      ∀ i, 𝒰.f i ≫ φ =
        productCoverDirectLocalAction μ A hA hNonempty hCompact i) :
    φ = globalSchemeAction μ A hA hNonempty hCompact := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
  apply 𝒰.hom_ext
  intro i
  rw [hφ i, globalSchemeAction_restrict]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeActionUniqueness
