import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamily
import QuaternionicSymmetry.ComplexProjectiveTorusPreservation

/-! The regular diagonal family carries actual cone equations to regular
functions vanishing on every complex-torus parameter and every cone point.
This does not yet identify the resulting relative vanishing ideal with
the extension of the cone ideal to the Laurent parameter ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyZeroIdeal

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalRegularFamily
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveTorusPreservation TorusLaurentRepresentation
open ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def familyZeroIdeal (A : Set (Space d)) :
    Ideal (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r)) :=
  ⨅ z : ComplexTorus r,
    ⨅ v : affineCone A,
      RingHom.ker (MvPolynomial.eval₂Hom (evalTorus z) v.1)

theorem mem_familyZeroIdeal_iff (A : Set (Space d))
    (p : MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r)) :
    p ∈ familyZeroIdeal (r := r) A ↔
      ∀ z : ComplexTorus r, ∀ v : Fin (d + 1) → ℂ,
        v ∈ affineCone A → MvPolynomial.eval₂ (evalTorus z) v p = 0 := by
  simp [familyZeroIdeal]

theorem familySubstitution_mem_familyZeroIdeal
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    {p : MvPolynomial (Fin (d + 1)) ℂ}
    (hp : p ∈ vanishingIdeal A) :
    familySubstitution μ p ∈ familyZeroIdeal (r := r) A := by
  rw [mem_familyZeroIdeal_iff]
  intro z v hv
  rw [eval₂_familySubstitution]
  have hAction := mapsTo_of_compact μ A hA hCompact z
  rw [mem_vanishingIdeal_iff] at hp
  exact hp _ (diagonal_maps_affineCone μ z A hAction hv)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyZeroIdeal
