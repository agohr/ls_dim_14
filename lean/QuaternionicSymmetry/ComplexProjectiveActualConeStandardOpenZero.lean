import QuaternionicSymmetry.ComplexProjectiveActualConeChartSaturation

/-! A numerator killed by the chosen coordinate represents zero in the
genuine homogeneous standard-open localization. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenZero

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
noncomputable section

variable {d : ℕ}

theorem away_mk_eq_zero_of_coordinate_mul_eq_zero
    (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) (n : ℕ)
    (q : MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A)
    (hq : q ∈ quotientPiece A n)
    (hzero : coordinateClass A i * q = 0) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    HomogeneousLocalization.Away.mk (quotientPiece A)
      (coordinateClass_mem_degreeOne A i) n q (by simpa using hq) = 0 := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  rw [HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨coordinateClass A i, ⟨1, by simp⟩⟩, ?_⟩
  exact hzero

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenZero
