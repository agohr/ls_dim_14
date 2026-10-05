import QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyIdealDescent
import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamily
import QuaternionicSymmetry.ComplexProjectiveTorusPreservation

/-! The actual regular diagonal family descends from ambient homogeneous
coordinates to the Laurent base change of the actual cone coordinate
quotient. This is a single algebraic family homomorphism, not merely a
collection of pointwise automorphisms. Its group-coaction and Proj
structure are developed separately. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalRegularQuotientFamily

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalRegularFamily
open ComplexProjectiveDiagonalFamilyZeroIdeal
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexProjectiveTorusPreservation
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem familySubstitution_mem_extendedConeIdeal
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    {p : MvPolynomial (Fin (d + 1)) ℂ}
    (hp : p ∈ vanishingIdeal A) :
    familySubstitution μ p ∈ extendedConeIdeal (r := r) A := by
  rw [← familyZeroIdeal_eq_extendedConeIdeal A]
  exact familySubstitution_mem_familyZeroIdeal μ A hA hCompact hp

/-- A genuine regular family on the cone quotient: its target is the
coordinate ring of the product with the algebraic complex torus. -/
def quotientFamilyHom
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) →+*
      (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
        extendedConeIdeal (r := r) A) :=
  Ideal.Quotient.lift (vanishingIdeal A)
    ((Ideal.Quotient.mk (extendedConeIdeal (r := r) A)).comp
      (familySubstitution μ))
    (by
      intro p hp
      change (Ideal.Quotient.mk (extendedConeIdeal (r := r) A))
        (familySubstitution μ p) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (familySubstitution_mem_extendedConeIdeal μ A hA hCompact hp))

@[simp] theorem quotientFamilyHom_mk
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (p : MvPolynomial (Fin (d + 1)) ℂ) :
    quotientFamilyHom μ A hA hCompact
      (Ideal.Quotient.mk (vanishingIdeal A) p) =
      Ideal.Quotient.mk (extendedConeIdeal (r := r) A)
        (familySubstitution μ p) := by
  rfl

/-- The descended regular family is a complex-algebra homomorphism,
not merely a ring homomorphism at each torus point. -/
def quotientFamilyAlgHom
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) →ₐ[ℂ]
      (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
        extendedConeIdeal (r := r) A) :=
  { quotientFamilyHom μ A hA hCompact with
    commutes' := by
      intro c
      change quotientFamilyHom μ A hA hCompact
          (Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.C c)) =
        Ideal.Quotient.mk (extendedConeIdeal (r := r) A)
          (MvPolynomial.C (algebraMap ℂ (TorusCoordinateRing r) c))
      rw [quotientFamilyHom_mk]
      simp [familySubstitution] }

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalRegularQuotientFamily
