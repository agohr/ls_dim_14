import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverMap
import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapComplexStructure
import QuaternionicSymmetry.CategoryPullbackProductOverlapIsoTransport
import QuaternionicSymmetry.CategoryPullbackProductOverlapAffineChart
import Mathlib.AlgebraicGeometry.Pullbacks

/-! An explicit composite version of the actual affine product-overlap
comparison. Unlike a rewrite-generated cast, every stage is a named iso,
so projection naturality can be applied without unfolding all stages. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapAffineExplicit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeBasicOpenOverlapIso
open ComplexProjectiveActualConeOverlapComplexStructure
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProjProductCoverMap
open CategoryPullbackProductOverlapIso
open CategoryPullbackProductOverlapIsoTransport
open ComplexProjectiveDiagonalAlgebraicCharts
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def actualConeProductOverlapAffineIsoExplicit
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) :=
        awayComplexAlgebra A hA hNonempty _
    let 𝒰 := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    pullback (𝒰.f i) (𝒰.f j) ≅
      Spec (CommRingCat.of
        ((TorusCoordinateRing r) ⊗[ℂ]
          HomogeneousLocalization.Away (quotientPiece A)
            (coordinateClass A i * coordinateClass A j))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty _
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r)))
  let g := actualConeProjToSpecComplex A hA hNonempty
  let u := (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
  let v := (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι
  let e := actualBasicOpenCoordinateOverlapIso A hA hNonempty i j
  have hs := actualBasicOpenOverlap_complexStructure A hA hNonempty i j
  change pullback
      ((actualConeTorusProductCoordinateCover (r := r) A hA hNonempty).f i)
      ((actualConeTorusProductCoordinateCover (r := r) A hA hNonempty).f j) ≅ _
  rw [actualConeTorusProductCover_f_eq_baseChangedOpenMap,
    actualConeTorusProductCover_f_eq_baseChangedOpenMap]
  exact baseChangedOverlapIso f g u v ≪≫
    asIso (overlapAffineBaseChange f g u v e) ≪≫
    pullback.congrHom rfl hs ≪≫
    pullbackSpecIso ℂ (TorusCoordinateRing r)
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j))

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapAffineExplicit
