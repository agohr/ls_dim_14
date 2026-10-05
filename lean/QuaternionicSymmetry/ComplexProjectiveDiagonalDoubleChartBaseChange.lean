import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleBaseChange
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamily

/-! The literal two-torus extension of an actual projective affine-chart
vanishing ideal, with both parameter inclusions on its coordinate ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartBaseChange

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

def doubleChartBaseChange : MvPolynomial (Fin d) ℂ →+*
    MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.map (algebraMap ℂ (DoubleTorusCoordinateRing r))

def doubleExtendedChartIdeal (A : Set (Space d)) (i : Fin (d + 1)) :
    Ideal (MvPolynomial (Fin d) (DoubleTorusCoordinateRing r)) :=
  Ideal.map (doubleChartBaseChange (r := r)) (chartVanishingIdeal A i)

def firstChartPolynomial :
    MvPolynomial (Fin d) (TorusCoordinateRing r) →+*
      MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.map (firstParameter (r := r))

def secondChartPolynomial :
    MvPolynomial (Fin d) (TorusCoordinateRing r) →+*
      MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.map (secondParameter (r := r))

theorem firstChartPolynomial_comp_baseChange :
    (firstChartPolynomial (r := r) (d := d)).comp
        (ComplexProjectiveDiagonalChartIdealDescent.chartBaseChange (r := r)) =
      doubleChartBaseChange (r := r) (d := d) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [firstChartPolynomial, doubleChartBaseChange,
      ComplexProjectiveDiagonalChartIdealDescent.chartBaseChange]
    exact congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
      firstParameter_comp_algebraMap
  · intro k
    simp [firstChartPolynomial, doubleChartBaseChange,
      ComplexProjectiveDiagonalChartIdealDescent.chartBaseChange]

theorem secondChartPolynomial_comp_baseChange :
    (secondChartPolynomial (r := r) (d := d)).comp
        (ComplexProjectiveDiagonalChartIdealDescent.chartBaseChange (r := r)) =
      doubleChartBaseChange (r := r) (d := d) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [secondChartPolynomial, doubleChartBaseChange,
      ComplexProjectiveDiagonalChartIdealDescent.chartBaseChange]
    exact congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
      secondParameter_comp_algebraMap
  · intro k
    simp [secondChartPolynomial, doubleChartBaseChange,
      ComplexProjectiveDiagonalChartIdealDescent.chartBaseChange]

theorem firstChartPolynomial_map_extendedChartIdeal
    (A : Set (Space d)) (i : Fin (d + 1)) :
    (extendedChartIdeal (r := r) A i).map firstChartPolynomial =
      doubleExtendedChartIdeal (r := r) A i := by
  simp only [extendedChartIdeal, doubleExtendedChartIdeal,
    Ideal.map_map, ← firstChartPolynomial_comp_baseChange]

theorem secondChartPolynomial_map_extendedChartIdeal
    (A : Set (Space d)) (i : Fin (d + 1)) :
    (extendedChartIdeal (r := r) A i).map secondChartPolynomial =
      doubleExtendedChartIdeal (r := r) A i := by
  simp only [extendedChartIdeal, doubleExtendedChartIdeal,
    Ideal.map_map, ← secondChartPolynomial_comp_baseChange]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartBaseChange
