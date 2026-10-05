import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoordinateCover
import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductAction

/-! The pulled-back global product cover has exactly the same affine chart
objects as the previously constructed literal torus × standard-open action. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeChartStructureCompatibility
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProjProductAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem actualConeTorusProductCover_X_eq_chartProduct
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    (actualConeTorusProductCoordinateCover (r := r) A hA hNonempty).X i =
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
        (chartStructureMap A hA hNonempty i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  rw [chartStructureMap_eq_globalRestriction]
  rfl

def actualConeProductCoverLocalAction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    (actualConeTorusProductCoordinateCover (r := r) A hA hNonempty).X i ⟶
      Proj (quotientPiece A) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact eqToHom (actualConeTorusProductCover_X_eq_chartProduct (r := r)
      A hA hNonempty i) ≫
    actualProjChartProductAction μ A hA hNonempty hCompact i ≫
      (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverCharts
