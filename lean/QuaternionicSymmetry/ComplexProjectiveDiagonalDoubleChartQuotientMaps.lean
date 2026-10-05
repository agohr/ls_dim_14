import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartBaseChange
import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleComultiplicationQuotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Genuine two-torus coefficient inclusions and multiplication on each
actual projective affine-chart quotient ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartQuotientMaps

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleChartBaseChange
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

def firstChartQuotient (A : Set (Space d)) (i : Fin (d + 1)) :
    (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸ extendedChartIdeal (r := r) A i) →+*
      (MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) ⧸
        doubleExtendedChartIdeal (r := r) A i) :=
  Ideal.quotientMap (doubleExtendedChartIdeal (r := r) A i)
    firstChartPolynomial
    (Ideal.map_le_iff_le_comap.mp
      (le_of_eq (firstChartPolynomial_map_extendedChartIdeal A i)))

def secondChartQuotient (A : Set (Space d)) (i : Fin (d + 1)) :
    (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸ extendedChartIdeal (r := r) A i) →+*
      (MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) ⧸
        doubleExtendedChartIdeal (r := r) A i) :=
  Ideal.quotientMap (doubleExtendedChartIdeal (r := r) A i)
    secondChartPolynomial
    (Ideal.map_le_iff_le_comap.mp
      (le_of_eq (secondChartPolynomial_map_extendedChartIdeal A i)))

def comultiplicationChartPolynomial :
    MvPolynomial (Fin d) (TorusCoordinateRing r) →+*
      MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.map (comultiplication (r := r))

theorem comultiplicationChartPolynomial_comp_baseChange :
    (comultiplicationChartPolynomial (r := r) (d := d)).comp
        (chartBaseChange (r := r)) =
      doubleChartBaseChange (r := r) (d := d) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [comultiplicationChartPolynomial, chartBaseChange, doubleChartBaseChange]
    exact congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
      ComplexProjectiveDiagonalDoubleComultiplicationQuotient.comultiplication_comp_algebraMap
  · intro k
    simp [comultiplicationChartPolynomial, chartBaseChange, doubleChartBaseChange]

theorem comultiplicationChartPolynomial_map_extendedChartIdeal
    (A : Set (Space d)) (i : Fin (d + 1)) :
    (extendedChartIdeal (r := r) A i).map comultiplicationChartPolynomial =
      doubleExtendedChartIdeal (r := r) A i := by
  simp only [extendedChartIdeal, doubleExtendedChartIdeal,
    Ideal.map_map, ← comultiplicationChartPolynomial_comp_baseChange]

def comultiplicationChartQuotient (A : Set (Space d)) (i : Fin (d + 1)) :
    (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸ extendedChartIdeal (r := r) A i) →+*
      (MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) ⧸
        doubleExtendedChartIdeal (r := r) A i) :=
  Ideal.quotientMap (doubleExtendedChartIdeal (r := r) A i)
    comultiplicationChartPolynomial
    (Ideal.map_le_iff_le_comap.mp
      (le_of_eq (comultiplicationChartPolynomial_map_extendedChartIdeal A i)))

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartQuotientMaps
