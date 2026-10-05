import QuaternionicSymmetry.ComplexTorusSchemeUnit
import QuaternionicSymmetry.ComplexProjectiveActualConeComplexStructure

/-! The identity section of the literal algebraic-torus product with the
actual homogeneous cone Proj. The scheme-action unit law is subsequent. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProductUnit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeComplexStructure
open ComplexTorusSchemeUnit
noncomputable section

variable {d : ℕ}

def actualConeProductUnit (r : ℕ)
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    Proj (quotientPiece A) ⟶
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
        (actualConeProjToSpecComplex A hA hNonempty) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let g := actualConeProjToSpecComplex A hA hNonempty
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r)))
  exact pullback.lift (g ≫ torusUnitSpec r) (𝟙 _) (by
    simp only [Category.assoc, torusUnitSpec_over_complex,
      Category.comp_id, Category.id_comp]
    rfl)

@[simp] theorem actualConeProductUnit_snd (r : ℕ)
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    actualConeProductUnit r A hA hNonempty ≫
      pullback.snd _ _ = 𝟙 (Proj (quotientPiece A)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  simp [actualConeProductUnit]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProductUnit
