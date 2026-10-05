import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverMap
import QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapIso

/-! The pairwise intersection of the literal torus × Proj coordinate-cover
objects is an actual base change of the affine homogeneous overlap. Its
structural map is obtained by transporting the single global Proj-to-Spec-ℂ
map; identifying that map with the canonical affine ℂ-structure is separate. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjProductOverlapIso

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProjProductCoverMap
open ComplexProjectiveActualConeBasicOpenOverlapIso
open CategoryPullbackProductOverlapIso
open ComplexProjectiveDiagonalAlgebraicCharts
noncomputable section

variable {r d : ℕ}

def actualConeTorusProductOverlapIso
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    let e := actualBasicOpenCoordinateOverlapIso A hA hNonempty i j
    pullback (𝒰.f i) (𝒰.f j) ≅
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
        (e.inv ≫
          overlapToOriginal
            (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
            (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι ≫
          actualConeProjToSpecComplex A hA hNonempty) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r)))
  let g := actualConeProjToSpecComplex A hA hNonempty
  let u := (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
  let v := (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι
  let e := actualBasicOpenCoordinateOverlapIso A hA hNonempty i j
  let m := pullback.map f (overlapToOriginal u v ≫ g)
    f (e.inv ≫ overlapToOriginal u v ≫ g)
    (𝟙 _) e.hom (𝟙 _) (by simp) (by simp)
  change pullback
      ((actualConeTorusProductCoordinateCover (r := r) A hA hNonempty).f i)
      ((actualConeTorusProductCoordinateCover (r := r) A hA hNonempty).f j) ≅
    pullback f (e.inv ≫ overlapToOriginal u v ≫ g)
  rw [actualConeTorusProductCover_f_eq_baseChangedOpenMap,
    actualConeTorusProductCover_f_eq_baseChangedOpenMap]
  exact baseChangedOverlapIso f g u v ≪≫ asIso m

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjProductOverlapIso
