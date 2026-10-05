import QuaternionicSymmetry.ComplexProjectiveActualConeUnitSectionCompatibility
import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeAction

/-! The glued regular torus-family morphism satisfies the genuine scheme
unit law on the literal actual cone Proj. Multiplication remains separate. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeGlobalUnitLaw

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProductUnit
open ComplexProjectiveActualConeLocalUnitLaw
open ComplexProjectiveActualConeUnitSectionCompatibility
open ComplexProjectiveActualConeGlobalSchemeAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem globalSchemeAction_unit
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    actualConeProductUnit r A hA hNonempty ≫
      globalSchemeAction μ A hA hNonempty hCompact =
    𝟙 (Proj (quotientPiece A)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let 𝒱 := actualConeCoordinateOpenCover A hA hNonempty
  apply 𝒱.hom_ext
  intro i
  change (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
      (actualConeProductUnit r A hA hNonempty ≫
        globalSchemeAction μ A hA hNonempty hCompact) =
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫ 𝟙 _
  rw [← Category.assoc, ← directBasicOpenUnit_global (r := r) A hA hNonempty i]
  simp only [Category.assoc]
  rw [globalSchemeAction_restrict μ A hA hNonempty hCompact i]
  exact directBasicOpenUnit_action μ A hA hNonempty hCompact i

end
end QuaternionicSymmetry.ComplexProjectiveActualConeGlobalUnitLaw
