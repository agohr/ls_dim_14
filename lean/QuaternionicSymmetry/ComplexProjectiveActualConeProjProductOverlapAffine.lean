import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductOverlapIso
import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapComplexStructure
import Mathlib.AlgebraicGeometry.Pullbacks

/-! Each pairwise overlap of the literal torus × actual cone `Proj` cover
is the genuine affine tensor-product scheme over the canonical complex
structure, not an independently equipped affine chart. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjProductOverlapAffine

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProjProductOverlapIso
open ComplexProjectiveActualConeOverlapComplexStructure
open ComplexProjectiveDiagonalAlgebraicCharts
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def actualConeTorusProductOverlapAffineIso
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
  have e := actualConeTorusProductOverlapIso (r := r) A hA hNonempty i j
  dsimp only at e
  rw [actualBasicOpenOverlap_complexStructure A hA hNonempty i j] at e
  exact e ≪≫
    (pullbackSpecIso ℂ (TorusCoordinateRing r)
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j)))

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjProductOverlapAffine
