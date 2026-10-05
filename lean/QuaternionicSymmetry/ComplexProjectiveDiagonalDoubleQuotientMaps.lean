import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleBaseChangeMaps

/-! Genuine quotient-ring maps induced by including either Laurent
parameter into the two-parameter coordinate ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleQuotientMaps

open ComplexProjectiveTopology ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleBaseChangeMaps
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

theorem firstIdeal_le_comap (A : Set (Space d)) :
    extendedConeIdeal (r := r) A ≤
      (doubleExtendedConeIdeal (r := r) A).comap (firstPolynomial (r := r)) := by
  intro p hp
  have h := Ideal.mem_map_of_mem (firstPolynomial (r := r)) hp
  rw [firstPolynomial_map_extendedConeIdeal] at h
  exact h

theorem secondIdeal_le_comap (A : Set (Space d)) :
    extendedConeIdeal (r := r) A ≤
      (doubleExtendedConeIdeal (r := r) A).comap (secondPolynomial (r := r)) := by
  intro p hp
  have h := Ideal.mem_map_of_mem (secondPolynomial (r := r)) hp
  rw [secondPolynomial_map_extendedConeIdeal] at h
  exact h

def firstQuotient (A : Set (Space d)) :
    (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
      extendedConeIdeal (r := r) A) →+*
    (MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) ⧸
      doubleExtendedConeIdeal (r := r) A) :=
  Ideal.quotientMap (doubleExtendedConeIdeal (r := r) A)
    (firstPolynomial (r := r)) (firstIdeal_le_comap A)

def secondQuotient (A : Set (Space d)) :
    (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
      extendedConeIdeal (r := r) A) →+*
    (MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) ⧸
      doubleExtendedConeIdeal (r := r) A) :=
  Ideal.quotientMap (doubleExtendedConeIdeal (r := r) A)
    (secondPolynomial (r := r)) (secondIdeal_le_comap A)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleQuotientMaps
