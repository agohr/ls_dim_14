import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalIteratedScheme

/-! The geometric projection of the actual local iterated Scheme map is
exactly the second-parameter local action, as a morphism into the literal
basic open (not only after mapping into the whole Proj). -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalIteratedGeometric

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenCoaction
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDirectProductIsoProjection
open ComplexProjectiveActualConeDoubleProductLocalAction
open ComplexProjectiveActualConeDoubleProductIsoProjection
open ComplexProjectiveActualConeDoubleLocalSecondFactor
open ComplexProjectiveActualConeStandardOpenParameterTensor
open ComplexProjectiveActualConeDoubleLocalIterated
open ComplexProjectiveActualConeDoubleLocalIteratedScheme
open ComplexProjectiveActualConeStandardOpenTwistRingNaturality
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem directBasicOpenDoubleIterated_snd
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    directBasicOpenDoubleIterated μ A hA hNonempty hCompact i ≫
      pullback.snd _ _ =
    directBasicOpenDoubleSecondFactor (r := r) A hA hNonempty i ≫
      directBasicOpenActionToBasicOpen μ A hA hNonempty hCompact i := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  let E₁ := directBasicOpenProductIso (r := r) A hA hNonempty i
  let E₂ := directBasicOpenDoubleProductIso (r := r) A hA hNonempty i
  let e := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)
  have h₁ : E₁.inv ≫ pullback.snd _ _ ≫ e.hom =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          HomogeneousLocalization.Away (quotientPiece A)
            (coordinateClass A i) →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))) := by
    rw [← directBasicOpenProductIso_hom_snd (r := r) A hA hNonempty i]
    simp [E₁]
  rw [← cancel_mono e.hom]
  change E₂.hom ≫
      Spec.map (CommRingCat.ofHom
        (secondStandardOpenTwist μ A hA hNonempty hCompact i)) ≫
      E₁.inv ≫ pullback.snd _ _ ≫ e.hom =
    E₂.hom ≫ Spec.map (CommRingCat.ofHom
      (secondParameterStandardOpen (r := r) A hA hNonempty i)) ≫
      E₁.inv ≫ E₁.hom ≫
      Spec.map (CommRingCat.ofHom
        (standardOpenCoaction μ A hA hNonempty hCompact i)) ≫
      e.inv ≫ e.hom
  rw [h₁]
  simp only [Iso.inv_hom_id_assoc]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [secondTwist_comp_includeRight μ A hA hNonempty hCompact i]
  rw [e.inv_hom_id, Category.comp_id]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalIteratedGeometric
