import QuaternionicSymmetry.ComplexProjectiveDiagonalGradedRingAction

/-! The literal homogeneous-coordinate quotient ring of an invariant
projective cutout inherits the diagonal ring automorphism. This is a
coordinate-ring construction, not a comparison theorem with the analytic
twistor manifold or a constructed closed Proj subscheme. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalCoordinateQuotient

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalIdealAutomorphism
open ComplexProjectiveDiagonalGradedRingAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem diagonalRingEquiv_map_vanishingIdeal
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z : ComplexTorus r) :
    (vanishingIdeal A).map (diagonalRingEquiv μ z) = vanishingIdeal A := by
  have hmap := Ideal.map_comap_of_equiv
    (I := vanishingIdeal A) (diagonalRingEquiv μ z)
  change (vanishingIdeal A).map (diagonalRingEquiv μ z) =
    (vanishingIdeal A).comap (diagonalRingEquiv μ z).symm at hmap
  rw [hmap]
  ext p
  change diagonalSubstitution μ z⁻¹ p ∈ vanishingIdeal A ↔
    p ∈ vanishingIdeal A
  exact diagonalSubstitution_mem_vanishingIdeal_iff μ A hA hCompact z⁻¹ p

def quotientRingEquiv
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z : ComplexTorus r) :
    (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) ≃+*
      (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) :=
  Ideal.quotientEquiv (vanishingIdeal A) (vanishingIdeal A)
    (diagonalRingEquiv μ z)
    (diagonalRingEquiv_map_vanishingIdeal μ A hA hCompact z).symm

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalCoordinateQuotient
