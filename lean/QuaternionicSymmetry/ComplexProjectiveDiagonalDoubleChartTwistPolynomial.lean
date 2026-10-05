import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartQuotientMaps
import QuaternionicSymmetry.ComplexProjectiveDiagonalAffineChartComorphism

/-! Raw polynomial two-torus coherence for the actual projective chart
weights `μ_(i.succAbove k) - μ_i`. Quotient descent is subsequent. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartTwistPolynomial

open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalAffineChartComorphism
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleChartBaseChange
open ComplexProjectiveDiagonalDoubleChartQuotientMaps
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

def firstChartTwist (μ : Fin (d + 1) → Fin r → ℤ) (i : Fin (d + 1)) :
    MvPolynomial (Fin d) (TorusCoordinateRing r) →+*
      MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (secondParameter (r := r)))
    (fun k => MvPolynomial.C
      (AddMonoidAlgebra.single (μ (i.succAbove k) - μ i, 0) 1) * MvPolynomial.X k)

def secondChartTwist (μ : Fin (d + 1) → Fin r → ℤ) (i : Fin (d + 1)) :
    MvPolynomial (Fin d) (TorusCoordinateRing r) →+*
      MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (firstParameter (r := r)))
    (fun k => MvPolynomial.C
      (AddMonoidAlgebra.single (0, μ (i.succAbove k) - μ i) 1) * MvPolynomial.X k)

theorem firstChartTwist_comp_baseChange
    (μ : Fin (d + 1) → Fin r → ℤ) (i : Fin (d + 1)) :
    (firstChartTwist μ i).comp (chartBaseChange (r := r)) =
      (firstChartPolynomial (r := r)).comp
        (chartActionComorphism μ i).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [firstChartTwist, chartBaseChange, firstChartPolynomial,
      chartActionComorphism]
    calc
      secondParameter (algebraMap ℂ (TorusCoordinateRing r) c) =
          algebraMap ℂ (DoubleTorusCoordinateRing r) c :=
        congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
          secondParameter_comp_algebraMap
      _ = firstParameter (algebraMap ℂ (TorusCoordinateRing r) c) :=
        (congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
          firstParameter_comp_algebraMap).symm
  · intro k
    simp [firstChartTwist, chartBaseChange, firstChartPolynomial,
      chartActionComorphism_X, regularChartCoordinate, firstParameter_monomial]

theorem secondChartTwist_comp_baseChange
    (μ : Fin (d + 1) → Fin r → ℤ) (i : Fin (d + 1)) :
    (secondChartTwist μ i).comp (chartBaseChange (r := r)) =
      (secondChartPolynomial (r := r)).comp
        (chartActionComorphism μ i).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [secondChartTwist, chartBaseChange, secondChartPolynomial,
      chartActionComorphism]
    calc
      firstParameter (algebraMap ℂ (TorusCoordinateRing r) c) =
          algebraMap ℂ (DoubleTorusCoordinateRing r) c :=
        congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
          firstParameter_comp_algebraMap
      _ = secondParameter (algebraMap ℂ (TorusCoordinateRing r) c) :=
        (congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
          secondParameter_comp_algebraMap).symm
  · intro k
    simp [secondChartTwist, chartBaseChange, secondChartPolynomial,
      chartActionComorphism_X, regularChartCoordinate, secondParameter_monomial]

theorem comultiplication_comp_chartAction_eq_first
    (μ : Fin (d + 1) → Fin r → ℤ) (i : Fin (d + 1)) :
    (comultiplicationChartPolynomial (r := r) (d := d)).comp
        (chartActionComorphism μ i).toRingHom =
      (firstChartTwist μ i).comp (chartActionComorphism μ i).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [comultiplicationChartPolynomial, chartActionComorphism,
      firstChartTwist, comultiplication, secondParameter]
  · intro k
    simp [comultiplicationChartPolynomial, chartActionComorphism_X,
      firstChartTwist, regularChartCoordinate, comultiplication_laurentMonomial,
      secondParameter_monomial, ← mul_assoc]
    simp [← map_mul, AddMonoidAlgebra.single_mul_single]

theorem comultiplication_comp_chartAction_eq_second
    (μ : Fin (d + 1) → Fin r → ℤ) (i : Fin (d + 1)) :
    (comultiplicationChartPolynomial (r := r) (d := d)).comp
        (chartActionComorphism μ i).toRingHom =
      (secondChartTwist μ i).comp (chartActionComorphism μ i).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [comultiplicationChartPolynomial, chartActionComorphism,
      secondChartTwist, comultiplication, firstParameter]
  · intro k
    simp [comultiplicationChartPolynomial, chartActionComorphism_X,
      secondChartTwist, regularChartCoordinate, comultiplication_laurentMonomial,
      firstParameter_monomial, ← mul_assoc]
    simp [← map_mul, AddMonoidAlgebra.single_mul_single]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartTwistPolynomial
