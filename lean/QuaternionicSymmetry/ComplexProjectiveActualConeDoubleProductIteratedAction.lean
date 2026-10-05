import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductMultiplication
import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalActionOverComplex
import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleBaseChange

/-! The literal iterated action on the two-torus × actual-Proj product is
formed by categorical pullbacks. Its second torus parameter acts first, and
the first parameter acts on the result. This is a genuine Scheme morphism,
not a pointwise permutation family. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductIteratedAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeGlobalSchemeAction
open ComplexProjectiveActualConeGlobalActionOverComplex
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def doubleTorusFirstSpec (r : ℕ) :
    Spec (CommRingCat.of (DoubleTorusCoordinateRing r)) ⟶
      Spec (CommRingCat.of (TorusCoordinateRing r)) :=
  Spec.map (CommRingCat.ofHom (firstParameter (r := r)))

def doubleTorusSecondSpec (r : ℕ) :
    Spec (CommRingCat.of (DoubleTorusCoordinateRing r)) ⟶
      Spec (CommRingCat.of (TorusCoordinateRing r)) :=
  Spec.map (CommRingCat.ofHom (secondParameter (r := r)))

theorem doubleTorusFirstSpec_over_complex (r : ℕ) :
    doubleTorusFirstSpec r ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (DoubleTorusCoordinateRing r))) := by
  simp only [doubleTorusFirstSpec, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [firstParameter_comp_algebraMap]

theorem doubleTorusSecondSpec_over_complex (r : ℕ) :
    doubleTorusSecondSpec r ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (DoubleTorusCoordinateRing r))) := by
  simp only [doubleTorusSecondSpec, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [secondParameter_comp_algebraMap]

def actualConeDoubleProductSecondFactor (r : ℕ)
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
  exact pullback.lift
    (pullback.fst f₂ g ≫ doubleTorusSecondSpec r)
    (pullback.snd f₂ g) (by
      simp only [Category.assoc, doubleTorusSecondSpec_over_complex]
      exact pullback.condition)

def actualConeDoubleProductIterated (r : ℕ)
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
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
  let b := actualConeDoubleProductSecondFactor r A hA hNonempty
  exact pullback.lift
    (pullback.fst f₂ g ≫ doubleTorusFirstSpec r)
    (b ≫ globalSchemeAction μ A hA hNonempty hCompact) (by
      have hfirst :
          (pullback.fst f₂ g ≫ doubleTorusFirstSpec r) ≫ f₁ =
            pullback.fst f₂ g ≫ f₂ := by
        rw [Category.assoc, doubleTorusFirstSpec_over_complex]
      have hsecond :
          (b ≫ globalSchemeAction μ A hA hNonempty hCompact) ≫ g =
            pullback.fst f₂ g ≫ f₂ := by
        rw [Category.assoc,
          globalSchemeAction_over_complex μ A hA hNonempty hCompact]
        change b ≫ pullback.fst f₁ g ≫ f₁ = _
        dsimp only [b, actualConeDoubleProductSecondFactor]
        rw [← Category.assoc, pullback.lift_fst,
          Category.assoc, doubleTorusSecondSpec_over_complex]
      calc
        (pullback.fst f₂ g ≫ doubleTorusFirstSpec r) ≫ f₁ =
            pullback.fst f₂ g ≫ f₂ := hfirst
        _ = pullback.snd f₂ g ≫ g := pullback.condition
        _ = (b ≫ globalSchemeAction μ A hA hNonempty hCompact) ≫ g :=
          (pullback.condition :
            pullback.fst f₂ g ≫ f₂ = pullback.snd f₂ g ≫ g).symm.trans hsecond.symm)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductIteratedAction
