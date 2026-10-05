import QuaternionicSymmetry.ComplexProjectiveActualConeDirectUnitProjection
import QuaternionicSymmetry.ComplexProjectiveActualConeProductUnit
import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverMap

/-! The local torus-unit specialization section is the restriction of the
literal global identity section of the torus × actual cone-Proj pullback. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeUnitSectionCompatibility

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProjProductCoverMap
open ComplexProjectiveActualConeProductUnit
open ComplexProjectiveActualConeLocalUnitLaw
open ComplexProjectiveActualConeDirectUnitProjection
open CategoryPullbackProductOverlapIso
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem directBasicOpenUnit_global
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    directBasicOpenUnit (r := r) A hA hNonempty i ≫ 𝒰.f i =
      (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProductUnit r A hA hNonempty := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
  dsimp only
  rw [actualConeTorusProductCover_f_eq_baseChangedOpenMap]
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangedOpenMap, pullback.lift_fst,
      directBasicOpenUnit_fst, actualConeProductUnit, pullback.lift_fst]
  · simp only [Category.assoc, baseChangedOpenMap, pullback.lift_snd,
      actualConeProductUnit]
    rw [← Category.assoc, directBasicOpenUnit_snd]
    simp

end
end QuaternionicSymmetry.ComplexProjectiveActualConeUnitSectionCompatibility
