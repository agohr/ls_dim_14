import QuaternionicSymmetry.ComplexProjectiveActualConeProjOverlap

/-! The overlap of the literal coordinate basic-open scheme cover is the
same affine homogeneous localization as Mathlib's `awayι` overlap. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapIso

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjOverlap
noncomputable section

variable {d : ℕ}

def actualBasicOpenCoordinateOverlapIso (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    pullback
      (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
      (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι ≅
    Spec (CommRingCat.of
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let ei := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)
  let ej := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A j)
    (coordinateClass_mem_degreeOne A j) (by omega)
  let m := pullback.map
    (Proj.awayι (quotientPiece A) (coordinateClass A i)
      (coordinateClass_mem_degreeOne A i) (by omega))
    (Proj.awayι (quotientPiece A) (coordinateClass A j)
      (coordinateClass_mem_degreeOne A j) (by omega))
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
    (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι
    ei.inv ej.inv (𝟙 _)
    (by simp [ei, Proj.basicOpenIsoSpec_inv_ι])
    (by simp [ej, Proj.basicOpenIsoSpec_inv_ι])
  exact (asIso m).symm ≪≫ actualProjCoordinateOverlapIso A hA hNonempty i j

end
end QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapIso
