import QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamily
import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamilySpecialization

/-! Specialization of the genuine Laurent-parameter chart quotient family at
an actual complex-torus point. This is the chart analogue of cone-quotient
specialization, needed for the scheme action counit. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilySpecialization

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartQuotientFamily
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def specializeChartQuotient (A : Set (Space d)) (i : Fin (d + 1))
    (z : ComplexTorus r) :
    (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸ extendedChartIdeal (r := r) A i) →+*
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) :=
  Ideal.Quotient.lift (extendedChartIdeal (r := r) A i)
    ((Ideal.Quotient.mk (chartVanishingIdeal A i)).comp
      (MvPolynomial.map (evalTorus z)))
    (by
      intro p hp
      change Ideal.Quotient.mk (chartVanishingIdeal A i)
        (MvPolynomial.map (evalTorus z) p) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← chartFamilyZeroIdeal_eq_extendedChartIdeal A i] at hp
      rw [mem_chartVanishingIdeal_iff]
      intro w hw
      rw [← MvPolynomial.eval₂_eq_eval_map]
      exact (mem_chartFamilyZeroIdeal_iff A i p).mp hp z w hw)

@[simp] theorem specializeChartQuotient_mk (A : Set (Space d))
    (i : Fin (d + 1)) (z : ComplexTorus r)
    (p : MvPolynomial (Fin d) (TorusCoordinateRing r)) :
    specializeChartQuotient A i z
      (Ideal.Quotient.mk (extendedChartIdeal (r := r) A i) p) =
    Ideal.Quotient.mk (chartVanishingIdeal A i)
      (MvPolynomial.map (evalTorus z) p) := rfl

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilySpecialization
