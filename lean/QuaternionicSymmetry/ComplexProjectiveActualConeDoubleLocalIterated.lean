import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleSecondFactorRestriction
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTwistRingNaturality
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoherence

/-! The actual affine standard-open two-step action, ordered as second
torus parameter first and first torus parameter second, is the Spec of the
checked second twist on the genuine tensor chart ring. Its composite with
the single local action is the literal two-parameter coaction. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalIterated

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenCoherence
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDoubleProductLocalAction
open ComplexProjectiveActualConeStandardOpenTwistRingNaturality
open ComplexProjectiveActualConeDoubleSecondFactorRestriction
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def directBasicOpenDoubleIterated
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    pullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (DoubleTorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) ⟶
    pullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (TorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (directBasicOpenDoubleProductIso (r := r) A hA hNonempty i).hom ≫
    Spec.map (CommRingCat.ofHom
      (secondStandardOpenTwist μ A hA hNonempty hCompact i)) ≫
    (directBasicOpenProductIso (r := r) A hA hNonempty i).inv

theorem directBasicOpenDoubleIterated_action
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    directBasicOpenDoubleIterated μ A hA hNonempty hCompact i ≫
      directBasicOpenProductAction μ A hA hNonempty hCompact i =
    directBasicOpenDoubleMultiplicationAction μ A hA hNonempty hCompact i := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  have hSpec :
      Spec.map (CommRingCat.ofHom
        (secondStandardOpenTwist μ A hA hNonempty hCompact i)) ≫
        Spec.map (CommRingCat.ofHom
          (standardOpenCoaction μ A hA hNonempty hCompact i)) =
      Spec.map (CommRingCat.ofHom
        ((secondStandardOpenTwist μ A hA hNonempty hCompact i).comp
          (standardOpenCoaction μ A hA hNonempty hCompact i))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  simp only [directBasicOpenDoubleIterated,
    directBasicOpenProductAction, directBasicOpenDoubleMultiplicationAction,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [standardOpen_comultiplication_second μ A hA hNonempty hCompact i]
  let e := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)
  simpa only [Category.assoc] using congrArg
    (fun q => (directBasicOpenDoubleProductIso (r := r) A hA hNonempty i).hom ≫
      q ≫ e.inv ≫ (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι)
    hSpec

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalIterated
