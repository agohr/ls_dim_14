import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularCoactionLaws
import QuaternionicSymmetry.ComplexProjectiveDiagonalAffineSchemeFamily

/-! Scheme-morphism form of the strict affine-cone quotient coaction laws.
This does not identify the Laurent base change with a scheme product and
does not yet construct an action on `Proj`. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalAffineSchemeLaws

open AlgebraicGeometry CategoryTheory
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexProjectiveDiagonalRegularQuotientFamily
open ComplexProjectiveDiagonalRegularFamilySpecialization
open ComplexProjectiveDiagonalFamilyCounit
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleQuotientCoaction
open ComplexProjectiveDiagonalDoubleComultiplicationQuotient
open ComplexProjectiveDiagonalRegularCoactionLaws
open ComplexProjectiveDiagonalAffineSchemeFamily
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem coneSchemeFamily_unit
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    Spec.map (CommRingCat.ofHom (specializeQuotient A 1)) ≫
        coneSchemeFamilyMap μ A hA hCompact =
      𝟙 (Spec (CommRingCat.of
        (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A))) := by
  rw [coneSchemeFamilyMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [quotientFamily_counit μ A hA hCompact]
  simp

theorem coneSchemeFamily_multiplication_first
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    Spec.map (CommRingCat.ofHom (comultiplicationQuotient A)) ≫
        coneSchemeFamilyMap μ A hA hCompact =
      Spec.map (CommRingCat.ofHom
        (firstTwistQuotient μ A hA hCompact)) ≫
        coneSchemeFamilyMap μ A hA hCompact := by
  rw [coneSchemeFamilyMap, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (quotientFamily_comultiplication_coherence μ A hA hCompact)

theorem coneSchemeFamily_multiplication_second
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    Spec.map (CommRingCat.ofHom (comultiplicationQuotient A)) ≫
        coneSchemeFamilyMap μ A hA hCompact =
      Spec.map (CommRingCat.ofHom
        (secondTwistQuotient μ A hA hCompact)) ≫
        coneSchemeFamilyMap μ A hA hCompact := by
  rw [coneSchemeFamilyMap, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (quotientFamily_comultiplication_second μ A hA hCompact)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalAffineSchemeLaws
