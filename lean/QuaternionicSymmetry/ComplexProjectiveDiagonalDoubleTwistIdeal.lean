import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleTwistPolynomial
import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularQuotientFamily

/-! Successive regular substitutions preserve the actual cone ideal
after two-parameter Laurent base change. The proof transports the
one-parameter ideal-preservation theorem through the exact base-change
maps, without a new invariant-cutout premise. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleTwistIdeal

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalRegularFamily
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexProjectiveDiagonalRegularQuotientFamily
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleBaseChangeMaps
open ComplexProjectiveDiagonalDoubleTwistPolynomial
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem firstTwist_map_extendedConeIdeal_le
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (extendedConeIdeal (r := r) A).map (firstTwist μ) ≤
      doubleExtendedConeIdeal (r := r) A := by
  have hpres : (vanishingIdeal A).map (familySubstitution μ) ≤
      extendedConeIdeal (r := r) A :=
    Ideal.map_le_iff_le_comap.mpr (by
      intro p hp
      exact familySubstitution_mem_extendedConeIdeal μ A hA hCompact hp)
  calc
    (extendedConeIdeal (r := r) A).map (firstTwist μ) =
        ((vanishingIdeal A).map (familySubstitution μ)).map
          (firstPolynomial (r := r)) := by
      rw [extendedConeIdeal, Ideal.map_map,
        firstTwist_comp_baseChange, ← Ideal.map_map]
    _ ≤ (extendedConeIdeal (r := r) A).map (firstPolynomial (r := r)) :=
      Ideal.map_mono hpres
    _ = doubleExtendedConeIdeal (r := r) A :=
      firstPolynomial_map_extendedConeIdeal A

theorem secondTwist_map_extendedConeIdeal_le
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    (extendedConeIdeal (r := r) A).map (secondTwist μ) ≤
      doubleExtendedConeIdeal (r := r) A := by
  have hpres : (vanishingIdeal A).map (familySubstitution μ) ≤
      extendedConeIdeal (r := r) A :=
    Ideal.map_le_iff_le_comap.mpr (by
      intro p hp
      exact familySubstitution_mem_extendedConeIdeal μ A hA hCompact hp)
  calc
    (extendedConeIdeal (r := r) A).map (secondTwist μ) =
        ((vanishingIdeal A).map (familySubstitution μ)).map
          (secondPolynomial (r := r)) := by
      rw [extendedConeIdeal, Ideal.map_map,
        secondTwist_comp_baseChange, ← Ideal.map_map]
    _ ≤ (extendedConeIdeal (r := r) A).map (secondPolynomial (r := r)) :=
      Ideal.map_mono hpres
    _ = doubleExtendedConeIdeal (r := r) A :=
      secondPolynomial_map_extendedConeIdeal A

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleTwistIdeal
