import QuaternionicSymmetry.ComplexProjectiveActualConeDirectProductIsoProjection
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenAlgCoaction
import QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenComplexStructure

/-! The literal local regular torus action is over the canonical `Spec ℂ`
structure on the actual cone Proj. This is the local premise needed to form
the genuinely iterated action by a categorical pullback. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalActionOverComplex

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
open ComplexProjectiveActualConeStandardOpenCoactionScalars
open ComplexProjectiveActualConeStandardOpenAlgCoaction
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDirectProductIsoProjection
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem directBasicOpenProductAction_over_complex
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    directBasicOpenProductAction μ A hA hNonempty hCompact i ≫
      actualConeProjToSpecComplex A hA hNonempty =
    pullback.fst _ _ ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  let e := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)
  have hbase : e.inv ≫
      (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
      actualConeProjToSpecComplex A hA hNonempty =
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (HomogeneousLocalization.Away
          (quotientPiece A) (coordinateClass A i)))) := by
    rw [← basicOpenIsoSpec_complexStructure A hA hNonempty i]
    simp [e]
  have hscalar :
      (standardOpenCoaction μ A hA hNonempty hCompact i).comp
        (algebraMap ℂ (HomogeneousLocalization.Away
          (quotientPiece A) (coordinateClass A i))) =
      algebraMap ℂ (TorusCoordinateRing r ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) := by
    ext c
    exact (standardOpenAlgCoaction μ A hA hNonempty hCompact i).commutes c
  unfold directBasicOpenProductAction
  simp only [Category.assoc] at hbase ⊢
  rw [hbase]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hscalar]
  -- Compare the affine tensor structure map with the first projection of
  -- the genuine pullback defining the local torus × standard-open product.
  rw [show (algebraMap ℂ
      (TorusCoordinateRing r ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i))) =
      (Algebra.TensorProduct.includeLeftRingHom :
        TorusCoordinateRing r →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A)
              (coordinateClass A i)).comp
        (algebraMap ℂ (TorusCoordinateRing r)) by
          ext c
          simp]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rw [← Category.assoc,
    directBasicOpenProductIso_hom_fst (r := r) A hA hNonempty i]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalActionOverComplex
