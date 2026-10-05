import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductCover
import QuaternionicSymmetry.ComplexTorusSchemeMultiplication
import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleComultiplicationQuotient

/-! Genuine multiplication on the first two torus factors of the literal
two-parameter torus product with the actual cone Proj. The middle scheme
map is induced by Laurent-character comultiplication, not a pointwise map. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductMultiplication

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeComplexStructure
open ComplexTorusLaurentComultiplication
open ComplexProjectiveDiagonalDoubleComultiplicationQuotient
noncomputable section

variable {r d : ℕ}

def doubleTorusMultiplicationSpec (r : ℕ) :
    Spec (CommRingCat.of (DoubleTorusCoordinateRing r)) ⟶
      Spec (CommRingCat.of (TorusCoordinateRing r)) :=
  Spec.map (CommRingCat.ofHom (comultiplication (r := r)))

theorem doubleTorusMultiplicationSpec_over_complex (r : ℕ) :
    doubleTorusMultiplicationSpec r ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (DoubleTorusCoordinateRing r))) := by
  simp only [doubleTorusMultiplicationSpec, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [comultiplication_comp_algebraMap]

def actualConeDoubleProductMultiplication (r : ℕ)
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    pullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (DoubleTorusCoordinateRing r))))
      (actualConeProjToSpecComplex A hA hNonempty) ⟶
    pullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (TorusCoordinateRing r))))
      (actualConeProjToSpecComplex A hA hNonempty) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let g := actualConeProjToSpecComplex A hA hNonempty
  let f₂ := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (DoubleTorusCoordinateRing r)))
  let f₁ := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (TorusCoordinateRing r)))
  exact pullback.lift
    (pullback.fst f₂ g ≫ doubleTorusMultiplicationSpec r)
    (pullback.snd f₂ g) (by
      simp only [Category.assoc, doubleTorusMultiplicationSpec_over_complex]
      exact pullback.condition)

@[simp] theorem actualConeDoubleProductMultiplication_snd (r : ℕ)
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    actualConeDoubleProductMultiplication r A hA hNonempty ≫
      pullback.snd _ _ = pullback.snd _ _ := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  simp [actualConeDoubleProductMultiplication]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductMultiplication
