import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenZero

/-! The genuine homogeneous standard-open ring is exactly the actual
affine-chart coordinate ring: injectivity follows from literal cone/chart
vanishing and the one-coordinate saturation lemma. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenInjective

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeDehomogenization
open ComplexProjectiveActualConeStandardOpenMap
open ComplexProjectiveActualConeStandardOpenFractions
open ComplexProjectiveActualConeChartSaturation
open ComplexProjectiveActualConeStandardOpenZero
noncomputable section

variable {d : ℕ}

theorem standardOpenToChart_injective (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    Function.Injective (standardOpenToChart A hA hNonempty i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  apply (RingHom.injective_iff_ker_eq_bot _).2
  apply (RingHom.ker_eq_bot_iff_eq_zero _).2
  intro x hx0
  obtain ⟨n, q, hq, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (quotientPiece A) (coordinateClass_mem_degreeOne A i) x
  have hqn : q ∈ quotientPiece A n := by simpa using hq
  rw [standardOpenToChart_mk A hA hNonempty i n q hqn] at hx0
  obtain ⟨p, hp, rfl⟩ := (mem_quotientPiece_iff A n q).mp hqn
  have hchart : dehomogenize i p ∈ chartVanishingIdeal A i := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [quotientDehomogenize] using hx0
  have hcone := chosen_times_mem_vanishingIdeal A i n p hp hchart
  have hzero : coordinateClass A i *
      (Ideal.Quotient.mk (vanishingIdeal A) p) = 0 := by
    simpa [coordinateClass] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr hcone)
  exact away_mk_eq_zero_of_coordinate_mul_eq_zero
    A hA hNonempty i n _ hqn hzero

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenInjective
