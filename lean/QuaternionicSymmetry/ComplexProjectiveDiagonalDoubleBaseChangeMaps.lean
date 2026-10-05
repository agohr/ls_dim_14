import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleBaseChange
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The two Laurent-parameter inclusions induce genuine algebraic maps
between the one-parameter and two-parameter cone quotients. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleBaseChangeMaps

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

def firstPolynomial :
    MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) →+*
      MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.map (firstParameter (r := r))

def secondPolynomial :
    MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) →+*
      MvPolynomial (Fin (d + 1)) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.map (secondParameter (r := r))

theorem firstPolynomial_comp_baseChange :
    (firstPolynomial (r := r) (d := d)).comp (baseChange (r := r)) =
      doubleBaseChange (r := r) (d := d) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [firstPolynomial, baseChange, doubleBaseChange,
      firstParameter_comp_algebraMap]
    exact congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
      firstParameter_comp_algebraMap
  · intro i
    simp [firstPolynomial, baseChange, doubleBaseChange]

theorem secondPolynomial_comp_baseChange :
    (secondPolynomial (r := r) (d := d)).comp (baseChange (r := r)) =
      doubleBaseChange (r := r) (d := d) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [secondPolynomial, baseChange, doubleBaseChange,
      secondParameter_comp_algebraMap]
    exact congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
      secondParameter_comp_algebraMap
  · intro i
    simp [secondPolynomial, baseChange, doubleBaseChange]

theorem firstPolynomial_map_extendedConeIdeal (A : Set (Space d)) :
    (extendedConeIdeal (r := r) A).map (firstPolynomial (r := r)) =
      doubleExtendedConeIdeal (r := r) A := by
  simp only [extendedConeIdeal, doubleExtendedConeIdeal,
    Ideal.map_map, ← firstPolynomial_comp_baseChange]

theorem secondPolynomial_map_extendedConeIdeal (A : Set (Space d)) :
    (extendedConeIdeal (r := r) A).map (secondPolynomial (r := r)) =
      doubleExtendedConeIdeal (r := r) A := by
  simp only [extendedConeIdeal, doubleExtendedConeIdeal,
    Ideal.map_map, ← secondPolynomial_comp_baseChange]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleBaseChangeMaps
