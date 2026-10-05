import QuaternionicSymmetry.ComplexProjectiveDiagonalVanishingIdeal
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The diagonal complex-torus substitution preserves both the affine-cone
vanishing ideal and the degree of each homogeneous equation. Compact
preservation suffices when the projective set has homogeneous equations. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalHomogeneousIdeal

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveTorusPreservation TorusLaurentRepresentation
open ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem diagonalSubstitution_isHomogeneous
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    {p : MvPolynomial (Fin (d + 1)) ℂ} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    (diagonalSubstitution μ z p).IsHomogeneous n := by
  change (MvPolynomial.eval₂ MvPolynomial.C
    (fun i => MvPolynomial.C (complexWeightCharacter (μ i) z : ℂ) *
      MvPolynomial.X i) p).IsHomogeneous n
  simpa only [one_mul] using hp.eval₂ MvPolynomial.C
    (fun i => MvPolynomial.C (complexWeightCharacter (μ i) z : ℂ) *
      MvPolynomial.X i)
    (fun c => MvPolynomial.isHomogeneous_C _ c)
    (fun i => (MvPolynomial.isHomogeneous_X ℂ i).C_mul _)

theorem diagonalSubstitution_mem_vanishingIdeal_of_compact
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z : ComplexTorus r)
    {p : MvPolynomial (Fin (d + 1)) ℂ}
    (hp : p ∈ vanishingIdeal A) :
    diagonalSubstitution μ z p ∈ vanishingIdeal A :=
  diagonalSubstitution_mem_vanishingIdeal μ z A
    (mapsTo_of_compact μ A hA hCompact z) hp

theorem diagonalSubstitution_homogeneous_vanishing_of_compact
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z : ComplexTorus r)
    {p : MvPolynomial (Fin (d + 1)) ℂ} {n : ℕ}
    (hp : p ∈ vanishingIdeal A) (hhom : p.IsHomogeneous n) :
    diagonalSubstitution μ z p ∈ vanishingIdeal A ∧
      (diagonalSubstitution μ z p).IsHomogeneous n :=
  ⟨diagonalSubstitution_mem_vanishingIdeal_of_compact μ A hA hCompact z hp,
    diagonalSubstitution_isHomogeneous μ z hhom⟩

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalHomogeneousIdeal
