import QuaternionicSymmetry.ComplexProjectiveDiagonalHomogeneousIdeal

/-! The full complex diagonal torus acts by inverse-pair polynomial
substitutions on the exact affine-cone vanishing ideal. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalIdealAutomorphism

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalHomogeneousIdeal
open ComplexProjectiveTorusPreservation TorusLaurentRepresentation
open ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem diagonalSubstitution_mem_vanishingIdeal_iff
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z : ComplexTorus r)
    (p : MvPolynomial (Fin (d + 1)) ℂ) :
    diagonalSubstitution μ z p ∈ vanishingIdeal A ↔
      p ∈ vanishingIdeal A := by
  constructor
  · intro hp
    rw [mem_vanishingIdeal_iff] at hp ⊢
    intro v hv
    have hv' := diagonal_maps_affineCone μ z⁻¹ A
      (mapsTo_of_compact μ A hA hCompact z⁻¹) hv
    have h := hp (diagonalEquiv μ z⁻¹ v) hv'
    rw [eval_diagonalSubstitution] at h
    have heq : diagonalEquiv μ z (diagonalEquiv μ z⁻¹ v) = v := by
      rw [← diagonalEquiv_mul, mul_inv_cancel, diagonalEquiv_one]
    simpa only [heq] using h
  · exact diagonalSubstitution_mem_vanishingIdeal_of_compact μ A hA hCompact z

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalIdealAutomorphism
