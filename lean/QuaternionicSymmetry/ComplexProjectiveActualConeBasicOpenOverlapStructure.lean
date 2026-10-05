import QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapIso
import QuaternionicSymmetry.CategoryPullbackProductOverlapIso

/-! The actual affine overlap comparison remains over the original cone
`Proj`: its map back is exactly Mathlib's homogeneous `awayι` for the
product coordinate. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapStructure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjOverlap
open ComplexProjectiveActualConeBasicOpenOverlapIso
open QuaternionicSymmetry.CategoryPullbackProductOverlapIso
noncomputable section

variable {d : ℕ}

theorem actualBasicOpenOverlapIso_inv_toProj
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    (actualBasicOpenCoordinateOverlapIso A hA hNonempty i j).inv ≫
      overlapToOriginal
        (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
        (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι =
      Proj.awayι (quotientPiece A) (coordinateClass A i * coordinateClass A j)
        (coordinateProduct_mem_degreeTwo A i j) (by omega) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  simp [actualBasicOpenCoordinateOverlapIso, overlapToOriginal, Category.assoc]
  rw [Proj.basicOpenIsoSpec_inv_ι]
  have h := Proj.pullbackAwayιIso_hom_awayι
    (quotientPiece A) (coordinateClass_mem_degreeOne A i) (by omega)
    (coordinateClass_mem_degreeOne A j) (by omega)
    (x := coordinateClass A i * coordinateClass A j) rfl
  rw [← h]
  simp [actualProjCoordinateOverlapIso, Proj.SpecMap_awayMap_awayι]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapStructure
