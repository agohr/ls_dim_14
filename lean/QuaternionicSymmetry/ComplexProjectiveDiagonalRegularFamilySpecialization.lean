import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularQuotientFamily
import QuaternionicSymmetry.ComplexProjectiveDiagonalCoordinateQuotient

/-! Every complex-torus fiber of the single regular quotient-family map
is exactly the previously proved pointwise coordinate automorphism. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamilySpecialization

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalRegularFamily
open ComplexProjectiveDiagonalFamilyZeroIdeal
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexProjectiveDiagonalRegularQuotientFamily
open ComplexProjectiveDiagonalCoordinateQuotient
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def specializeQuotient (A : Set (Space d)) (z : ComplexTorus r) :
    (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
        extendedConeIdeal (r := r) A) →+*
      (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) :=
  Ideal.Quotient.lift (extendedConeIdeal (r := r) A)
    ((Ideal.Quotient.mk (vanishingIdeal A)).comp
      (MvPolynomial.map (evalTorus z)))
    (by
      intro p hp
      change Ideal.Quotient.mk (vanishingIdeal A)
        (MvPolynomial.map (evalTorus z) p) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← familyZeroIdeal_eq_extendedConeIdeal A] at hp
      rw [mem_vanishingIdeal_iff]
      intro v hv
      rw [← MvPolynomial.eval₂_eq_eval_map]
      exact (mem_familyZeroIdeal_iff A p).mp hp z v hv)

theorem specializeQuotient_mk (A : Set (Space d))
    (z : ComplexTorus r)
    (p : MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r)) :
    specializeQuotient A z
      (Ideal.Quotient.mk (extendedConeIdeal (r := r) A) p) =
    Ideal.Quotient.mk (vanishingIdeal A)
      (MvPolynomial.map (evalTorus z) p) := rfl

theorem specialize_quotientFamilyHom
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z : ComplexTorus r)
    (q : MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) :
    specializeQuotient A z (quotientFamilyHom μ A hA hCompact q) =
      quotientRingEquiv μ A hA hCompact z q := by
  induction q using Quotient.inductionOn' with
  | _ p =>
    change specializeQuotient A z
      (quotientFamilyHom μ A hA hCompact
        (Ideal.Quotient.mk (vanishingIdeal A) p)) =
      quotientRingEquiv μ A hA hCompact z
        (Ideal.Quotient.mk (vanishingIdeal A) p)
    rw [quotientFamilyHom_mk, specializeQuotient_mk]
    change Ideal.Quotient.mk (vanishingIdeal A)
        (((MvPolynomial.map (evalTorus z)).comp (familySubstitution μ)) p) = _
    rw [specialize_familySubstitution]
    simp [quotientRingEquiv,
      ComplexProjectiveDiagonalGradedRingAction.diagonalRingEquiv]
    rfl

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamilySpecialization
