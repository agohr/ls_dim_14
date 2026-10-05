import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalIterated
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalSecondFactorScheme
import QuaternionicSymmetry.ComplexProjectiveActualConeDirectProductIsoProjection
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductIsoProjection

/-! The locally iterated Scheme action has the first torus parameter as its
torus projection. Its geometric projection is the actual second-parameter
local action, proved below using exact standard-open coaction naturality. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalIteratedScheme

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
open ComplexProjectiveActualConeDoubleLocalIterated
open ComplexProjectiveActualConeStandardOpenTwistRingNaturality
open ComplexProjectiveActualConeDoubleProductIteratedAction
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem directBasicOpenDoubleIterated_fst
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    directBasicOpenDoubleIterated μ A hA hNonempty hCompact i ≫
      pullback.fst _ _ =
    pullback.fst _ _ ≫ doubleTorusFirstSpec r := by
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
        (secondStandardOpenTwist μ A hA hNonempty hCompact i)) ≫
      E₁.inv ≫ pullback.fst _ _ = _
  rw [h₁]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [secondTwist_comp_includeLeft μ A hA hNonempty hCompact i]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rw [← Category.assoc,
    directBasicOpenDoubleProductIso_hom_fst (r := r) A hA hNonempty i]
  rfl

def directBasicOpenActionToBasicOpen
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    pullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (TorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) ⟶
    Proj.basicOpen (quotientPiece A) (coordinateClass A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (directBasicOpenProductIso (r := r) A hA hNonempty i).hom ≫
    Spec.map (CommRingCat.ofHom
      (standardOpenCoaction μ A hA hNonempty hCompact i)) ≫
    (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
      (coordinateClass_mem_degreeOne A i) (by omega)).inv

theorem directBasicOpenActionToBasicOpen_comp_ι
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    directBasicOpenActionToBasicOpen μ A hA hNonempty hCompact i ≫
      (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι =
    directBasicOpenProductAction μ A hA hNonempty hCompact i := rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalIteratedScheme
