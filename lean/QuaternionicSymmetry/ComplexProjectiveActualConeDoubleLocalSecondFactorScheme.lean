import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalSecondFactor
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductIsoProjection
import QuaternionicSymmetry.ComplexProjectiveActualConeDirectProductIsoProjection

/-! The local second-factor map is the genuine product projection: the
second torus parameter is selected, and the geometric coordinate is fixed. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalSecondFactorScheme

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDirectProductIsoProjection
open ComplexProjectiveActualConeDoubleProductLocalAction
open ComplexProjectiveActualConeDoubleProductIsoProjection
open ComplexProjectiveActualConeDoubleLocalSecondFactor
open ComplexProjectiveActualConeStandardOpenParameterTensor
open ComplexProjectiveActualConeDoubleProductIteratedAction
open ComplexTorusLaurentComultiplication
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem directBasicOpenDoubleSecondFactor_fst
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    directBasicOpenDoubleSecondFactor (r := r) A hA hNonempty i ≫
      pullback.fst _ _ =
    pullback.fst _ _ ≫ doubleTorusSecondSpec r := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  let E₁ := directBasicOpenProductIso (r := r) A hA hNonempty i
  let E₂ := directBasicOpenDoubleProductIso (r := r) A hA hNonempty i
  have h₁ : E₁.inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          TorusCoordinateRing r →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))) := by
    rw [← directBasicOpenProductIso_hom_fst (r := r) A hA hNonempty i]
    simp [E₁]
  change E₂.hom ≫
      Spec.map (CommRingCat.ofHom
        (secondParameterStandardOpen (r := r) A hA hNonempty i)) ≫
      E₁.inv ≫ pullback.fst _ _ = _
  rw [h₁]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [secondParameterStandardOpen_comp_includeLeft (r := r) A hA hNonempty i]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rw [← Category.assoc,
    directBasicOpenDoubleProductIso_hom_fst (r := r) A hA hNonempty i]
  rfl

set_option maxRecDepth 2048 in
theorem directBasicOpenDoubleSecondFactor_snd
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    directBasicOpenDoubleSecondFactor (r := r) A hA hNonempty i ≫
      pullback.snd _ _ = pullback.snd _ _ := by
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
        (secondParameterStandardOpen (r := r) A hA hNonempty i)) ≫
      E₁.inv ≫ pullback.snd _ _ ≫ e.hom =
    pullback.snd _ _ ≫ e.hom
  rw [h₁]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [secondParameterStandardOpen_comp_includeRight (r := r) A hA hNonempty i]
  exact directBasicOpenDoubleProductIso_hom_snd (r := r) A hA hNonempty i

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalSecondFactorScheme
