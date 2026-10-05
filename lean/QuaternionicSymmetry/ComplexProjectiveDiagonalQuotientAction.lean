import QuaternionicSymmetry.ComplexProjectiveDiagonalCoordinateActionCoherence

/-! The invariant affine-cone coordinate quotient carries a coherent
complex-torus action by ℂ-algebra-preserving ring automorphisms. This is
not yet a Proj-scheme action or an analytic/algebraic comparison. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalQuotientAction

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalCoordinateQuotient
open ComplexProjectiveDiagonalCoordinateActionCoherence
open ComplexProjectiveDiagonalGradedRingAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem quotientRingEquiv_one
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    quotientRingEquiv μ A hA hCompact 1 = 1 := by
  apply RingEquiv.ext
  intro q
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  change Ideal.Quotient.mk (vanishingIdeal A) (diagonalSubstitution μ 1 p) =
    Ideal.Quotient.mk (vanishingIdeal A) p
  rw [diagonalSubstitution_one]
  rfl

theorem quotientRingEquiv_mul
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z w : ComplexTorus r) :
    quotientRingEquiv μ A hA hCompact (z * w) =
      quotientRingEquiv μ A hA hCompact z *
        quotientRingEquiv μ A hA hCompact w := by
  apply RingEquiv.ext
  intro q
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  change Ideal.Quotient.mk (vanishingIdeal A)
      (diagonalSubstitution μ (z * w) p) =
    Ideal.Quotient.mk (vanishingIdeal A)
      (diagonalSubstitution μ z (diagonalSubstitution μ w p))
  rw [diagonalSubstitution_mul]
  rfl

def quotientCoordinateAction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    ComplexTorus r →* RingEquiv
      (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A)
      (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) where
  toFun := quotientRingEquiv μ A hA hCompact
  map_one' := quotientRingEquiv_one μ A hA hCompact
  map_mul' := quotientRingEquiv_mul μ A hA hCompact

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalQuotientAction
