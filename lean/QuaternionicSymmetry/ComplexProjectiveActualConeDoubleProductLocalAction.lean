import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductCover
import QuaternionicSymmetry.ComplexProjectiveActualConeDirectLocalSchemeAction
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoaction

/-! The literal double-torus product basic open is the affine spectrum of
the actual two-parameter homogeneous standard-open tensor ring. The checked
coaction/comultiplication composite therefore gives a genuine local Scheme
morphism on this product, pending the global multiplication comparison. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductLocalAction

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
open ComplexProjectiveActualConeDoubleStandardOpenCoaction
open ComplexProjectiveActualConeDoubleProductCover
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def directBasicOpenDoubleProductIso (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    pullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (DoubleTorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) ≅
      Spec (CommRingCat.of ((DoubleTorusCoordinateRing r) ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  let f := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (DoubleTorusCoordinateRing r)))
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
  exact asIso m ≪≫ (pullbackSpecIso ℂ (DoubleTorusCoordinateRing r)
    (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)))

def directBasicOpenDoubleMultiplicationAction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    pullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (DoubleTorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) ⟶
      Proj (quotientPiece A) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (directBasicOpenDoubleProductIso (r := r) A hA hNonempty i).hom ≫
    Spec.map (CommRingCat.ofHom
      ((comultiplicationStandardOpen (r := r) A hA hNonempty i).comp
        (standardOpenCoaction μ A hA hNonempty hCompact i))) ≫
    (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
      (coordinateClass_mem_degreeOne A i) (by omega)).inv ≫
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductLocalAction
