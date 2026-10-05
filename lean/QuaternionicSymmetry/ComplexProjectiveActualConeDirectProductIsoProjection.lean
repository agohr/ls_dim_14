import QuaternionicSymmetry.ComplexProjectiveActualConeDirectLocalSchemeAction

/-! Explicit projection identity for the genuine affine-product chart iso;
this connects torus-unit specialization to the literal product pullback. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDirectProductIsoProjection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeDirectLocalSchemeAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem directBasicOpenProductIso_hom_snd
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (directBasicOpenProductIso (r := r) A hA hNonempty i).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          HomogeneousLocalization.Away (quotientPiece A)
            (coordinateClass A i) →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))) =
    pullback.snd _ _ ≫
      (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
        (coordinateClass_mem_degreeOne A i) (by omega)).hom := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  simp [directBasicOpenProductIso, Category.assoc,
    pullbackSpecIso_hom_snd, pullback.map]

theorem directBasicOpenProductIso_hom_fst
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (directBasicOpenProductIso (r := r) A hA hNonempty i).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          TorusCoordinateRing r →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))) =
    pullback.fst _ _ := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  simp [directBasicOpenProductIso, Category.assoc,
    pullbackSpecIso_hom_fst, pullback.map]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDirectProductIsoProjection
