import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleComultiplicationQuotient
import QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyCounit

/-! Literal counit and multiplication/coassociativity laws for the
Laurent-parameter regular action on the actual affine-cone coordinate
quotient. All equalities are between ring homomorphisms of coordinate
rings, not merely on complex points. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalRegularCoactionLaws

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalRegularQuotientFamily
open ComplexProjectiveDiagonalRegularFamilySpecialization
open ComplexProjectiveDiagonalFamilyCounit
open ComplexProjectiveDiagonalDoubleQuotientCoaction
open ComplexProjectiveDiagonalDoubleComultiplicationQuotient
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem quotientFamily_comultiplication_second
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (comultiplicationQuotient A).comp
        (quotientFamilyHom μ A hA hCompact) =
      (secondTwistQuotient μ A hA hCompact).comp
        (quotientFamilyHom μ A hA hCompact) :=
  (quotientFamily_comultiplication_coherence μ A hA hCompact).trans
    (quotientFamily_twoParameter_coherence μ A hA hCompact)

theorem regularConeActionLaws
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (specializeQuotient A 1).comp (quotientFamilyHom μ A hA hCompact) =
        RingHom.id (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) ∧
      (comultiplicationQuotient A).comp
          (quotientFamilyHom μ A hA hCompact) =
        (firstTwistQuotient μ A hA hCompact).comp
          (quotientFamilyHom μ A hA hCompact) ∧
      (comultiplicationQuotient A).comp
          (quotientFamilyHom μ A hA hCompact) =
        (secondTwistQuotient μ A hA hCompact).comp
          (quotientFamilyHom μ A hA hCompact) :=
  ⟨quotientFamily_counit μ A hA hCompact,
    quotientFamily_comultiplication_coherence μ A hA hCompact,
    quotientFamily_comultiplication_second μ A hA hCompact⟩

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalRegularCoactionLaws
