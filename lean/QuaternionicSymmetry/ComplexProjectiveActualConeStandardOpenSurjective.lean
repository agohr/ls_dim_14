import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoordinates

/-! The genuine homogeneous standard-open ring maps onto the actual
affine chart quotient. Injectivity, which encodes saturation, is separate. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenSurjective

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
open ComplexProjectiveActualConeStandardOpenCoordinates
noncomputable section

variable {d : ℕ}

theorem standardOpenToChart_surjective (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    Function.Surjective (standardOpenToChart A hA hNonempty i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hC : (Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.C a)) ∈
          quotientPiece A 0 :=
        (mem_quotientPiece_iff A 0 _).mpr
          ⟨MvPolynomial.C a,
            MvPolynomial.isHomogeneous_C (Fin (d + 1)) a, rfl⟩
      refine ⟨HomogeneousLocalization.Away.mk (quotientPiece A)
        (coordinateClass_mem_degreeOne A i) 0
        (Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.C a)) hC, ?_⟩
      · rw [standardOpenToChart_mk A hA hNonempty i 0 _ hC]
        simp [quotientDehomogenize, dehomogenize]
  | add p q hp hq =>
      obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv⟩ := hq
      refine ⟨u + v, ?_⟩
      simp [map_add, hu, hv]
  | mul_X p k hp =>
      obtain ⟨u, hu⟩ := hp
      refine ⟨u * HomogeneousLocalization.Away.mk (quotientPiece A)
        (coordinateClass_mem_degreeOne A i) 1
        (coordinateClass A (i.succAbove k))
        (coordinateClass_mem_degreeOne A (i.succAbove k)), ?_⟩
      simp [map_mul, hu, standardOpenToChart_coordinate]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenSurjective
