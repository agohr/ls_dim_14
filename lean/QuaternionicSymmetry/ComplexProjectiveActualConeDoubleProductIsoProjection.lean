import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductLocalAction

/-! Projection identities for the genuine affine-product iso with the
literal two-parameter complex torus coordinate ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductIsoProjection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeDoubleProductLocalAction
open ComplexTorusLaurentComultiplication
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem directBasicOpenDoubleProductIso_hom_snd
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (directBasicOpenDoubleProductIso (r := r) A hA hNonempty i).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          HomogeneousLocalization.Away (quotientPiece A)
            (coordinateClass A i) →+*
          DoubleTorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))) =
    pullback.snd _ _ ≫
      (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
        (coordinateClass_mem_degreeOne A i) (by omega)).hom := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  simp [directBasicOpenDoubleProductIso, Category.assoc,
    pullbackSpecIso_hom_snd, pullback.map]

theorem directBasicOpenDoubleProductIso_hom_fst
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (directBasicOpenDoubleProductIso (r := r) A hA hNonempty i).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          DoubleTorusCoordinateRing r →+*
          DoubleTorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))) =
    pullback.fst _ _ := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  simp [directBasicOpenDoubleProductIso, Category.assoc,
    pullbackSpecIso_hom_fst, pullback.map]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductIsoProjection
