import QuaternionicSymmetry.ComplexProjectiveDiagonalQuotientAction

/-! The coherent coordinate-quotient action fixes scalars, hence consists
of genuine complex-algebra automorphisms. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalQuotientAlgAction

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalCoordinateQuotient
open ComplexProjectiveDiagonalQuotientAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def quotientAlgEquiv
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z : ComplexTorus r) :
    (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) ≃ₐ[ℂ]
      (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) :=
  AlgEquiv.ofRingEquiv (f := quotientRingEquiv μ A hA hCompact z) (by
    intro c
    change Ideal.Quotient.mk (vanishingIdeal A)
        (ComplexProjectiveDiagonalVanishingIdeal.diagonalSubstitution μ z
          (MvPolynomial.C c)) =
      Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.C c)
    simp [ComplexProjectiveDiagonalVanishingIdeal.diagonalSubstitution])

theorem quotientAlgEquiv_one
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    quotientAlgEquiv μ A hA hCompact 1 = 1 := by
  apply AlgEquiv.ext
  intro q
  exact congrFun (congrArg (fun f : _ ≃+* _ => (f : _ → _))
    (quotientRingEquiv_one μ A hA hCompact)) q

theorem quotientAlgEquiv_mul
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z w : ComplexTorus r) :
    quotientAlgEquiv μ A hA hCompact (z * w) =
      quotientAlgEquiv μ A hA hCompact z *
        quotientAlgEquiv μ A hA hCompact w := by
  apply AlgEquiv.ext
  intro q
  exact congrFun (congrArg (fun f : _ ≃+* _ => (f : _ → _))
    (quotientRingEquiv_mul μ A hA hCompact z w)) q

def quotientCoordinateAlgAction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    ComplexTorus r →* ((MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) ≃ₐ[ℂ]
      (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A)) where
  toFun := quotientAlgEquiv μ A hA hCompact
  map_one' := quotientAlgEquiv_one μ A hA hCompact
  map_mul' := quotientAlgEquiv_mul μ A hA hCompact

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalQuotientAlgAction
