import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCounit
import QuaternionicSymmetry.ComplexProjectiveActualConeDirectLocalSchemeAction

/-! The honest torus-unit specialization on an actual homogeneous
standard-open affine chart is a left inverse to its regular local action.
Comparison of this local section with the pullback of the global product
unit is a separate naturality statement. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalUnitLaw

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenCounit
open ComplexProjectiveActualConeDirectLocalSchemeAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def directBasicOpenUnit (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).toScheme ⟶
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
        ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
          ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
            A hA hNonempty) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
      (coordinateClass_mem_degreeOne A i) (by omega)).hom ≫
    Spec.map (CommRingCat.ofHom
      (specializeStandardOpen (r := r) A hA hNonempty i 1)) ≫
    (directBasicOpenProductIso (r := r) A hA hNonempty i).inv

theorem directBasicOpenUnit_action
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    directBasicOpenUnit (r := r) A hA hNonempty i ≫
      directBasicOpenProductAction μ A hA hNonempty hCompact i =
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  have hsc :
      Spec.map (CommRingCat.ofHom
          (specializeStandardOpen (r := r) A hA hNonempty i 1)) ≫
        Spec.map (CommRingCat.ofHom
          (standardOpenCoaction μ A hA hNonempty hCompact i)) =
      𝟙 (Spec (CommRingCat.of (HomogeneousLocalization.Away
        (quotientPiece A) (coordinateClass A i)))) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [standardOpenCoaction_counit μ A hA hNonempty hCompact i]
    simp
  simp only [directBasicOpenUnit, directBasicOpenProductAction, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  have hm :
      ((Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
          (coordinateClass_mem_degreeOne A i) (by omega)).hom ≫
        Spec.map (CommRingCat.ofHom
          (specializeStandardOpen (r := r) A hA hNonempty i 1))) ≫
        Spec.map (CommRingCat.ofHom
          (standardOpenCoaction μ A hA hNonempty hCompact i)) =
      (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
        (coordinateClass_mem_degreeOne A i) (by omega)).hom := by
    rw [Category.assoc, hsc]
    simp
  rw [hm]
  simp

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalUnitLaw
