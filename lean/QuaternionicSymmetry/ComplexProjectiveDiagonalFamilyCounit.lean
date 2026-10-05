import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamilySpecialization
import QuaternionicSymmetry.ComplexProjectiveDiagonalQuotientAction

/-! The regular quotient-family homomorphism satisfies the counit law:
specializing its torus parameter at the identity is the identity map of
the actual cone coordinate quotient. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyCounit

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalRegularQuotientFamily
open ComplexProjectiveDiagonalRegularFamilySpecialization
open ComplexProjectiveDiagonalQuotientAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem quotientFamily_counit
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (specializeQuotient A 1).comp (quotientFamilyHom μ A hA hCompact) =
      RingHom.id (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) := by
  apply RingHom.ext
  intro q
  change specializeQuotient A 1 (quotientFamilyHom μ A hA hCompact q) = q
  rw [specialize_quotientFamilyHom]
  rw [quotientRingEquiv_one]
  rfl

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyCounit
