import QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenComplexStructure
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoaction
import Mathlib.AlgebraicGeometry.Pullbacks

/-! A direct local regular scheme action on the literal product with each
actual cone-Proj basic open. It is obtained from the checked homogeneous
standard-open coaction via the genuine affine product iso. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDirectLocalSchemeAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeBasicOpenComplexStructure
open ComplexProjectiveActualConeStandardOpenCoaction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def directBasicOpenProductIso (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) ≅
      Spec (CommRingCat.of ((TorusCoordinateRing r) ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r)))
  let e := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i))))
  let m := pullback.map f
    ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
      actualConeProjToSpecComplex A hA hNonempty)
    f g (𝟙 _) e.hom (𝟙 _) (by simp)
    (by simpa using (basicOpenIsoSpec_complexStructure A hA hNonempty i).symm)
  exact asIso m ≪≫ (pullbackSpecIso ℂ (TorusCoordinateRing r)
    (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)))

def directBasicOpenProductAction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) ⟶
      Proj (quotientPiece A) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (directBasicOpenProductIso (r := r) A hA hNonempty i).hom ≫
    Spec.map (CommRingCat.ofHom
      (standardOpenCoaction μ A hA hNonempty hCompact i)) ≫
    (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
      (coordinateClass_mem_degreeOne A i) (by omega)).inv ≫
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDirectLocalSchemeAction
