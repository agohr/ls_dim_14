import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductLocalAction
import QuaternionicSymmetry.ComplexProjectiveActualConeDirectLocalSchemeAction
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenComultiplicationTensor
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductMultiplication

/-! The actual affine standard-open multiplication map is the Spec of the
literal Laurent comultiplication tensor identity, transported through the
two genuine affine-product isomorphisms. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalMultiplication

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
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDoubleProductLocalAction
open ComplexProjectiveActualConeStandardOpenComultiplicationTensor
open ComplexProjectiveActualConeDoubleProductMultiplication
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def directBasicOpenDoubleMultiplication
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
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
      (comultiplicationStandardOpen (r := r) A hA hNonempty i)) ≫
    (directBasicOpenProductIso (r := r) A hA hNonempty i).inv

theorem directBasicOpenDoubleMultiplication_action
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    directBasicOpenDoubleMultiplication (r := r) A hA hNonempty i ≫
      directBasicOpenProductAction μ A hA hNonempty hCompact i =
    directBasicOpenDoubleMultiplicationAction μ A hA hNonempty hCompact i := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  simp [directBasicOpenDoubleMultiplication,
    directBasicOpenProductAction,
    directBasicOpenDoubleMultiplicationAction, Category.assoc]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalMultiplication
