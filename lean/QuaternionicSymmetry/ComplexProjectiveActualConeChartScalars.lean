import QuaternionicSymmetry.ComplexProjectiveActualConeComplexStructure
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenFractions

/-! The actual standard-open comparison preserves the canonical complex
scalars coming from the single global degree-zero map. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeChartScalars

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeDehomogenization
open ComplexProjectiveActualConeDegreeZeroScalars
open ComplexProjectiveActualConeStandardOpenMap
open ComplexProjectiveActualConeStandardOpenFractions
noncomputable section

variable {d : ℕ}

theorem standardOpenToChart_scalar (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) (c : ℂ) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    standardOpenToChart A hA hNonempty i
      (HomogeneousLocalization.fromZeroRingHom (quotientPiece A)
        (Submonoid.powers (coordinateClass A i))
        (scalarToDegreeZero A hA hNonempty c)) =
      algebraMap ℂ (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) c := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  have hq := scalar_mem_degreeZero A c
  have hfrom :
      HomogeneousLocalization.fromZeroRingHom (quotientPiece A)
        (Submonoid.powers (coordinateClass A i))
        (scalarToDegreeZero A hA hNonempty c) =
      HomogeneousLocalization.Away.mk (quotientPiece A)
      (coordinateClass_mem_degreeOne A i) 0
      (algebraMap ℂ (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) c) hq := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.fromZeroRingHom,
      HomogeneousLocalization.Away.val_mk,
      HomogeneousLocalization.val_mk, scalarToDegreeZero_coe]
  rw [hfrom]
  rw [standardOpenToChart_mk A hA hNonempty i 0 _ hq]
  have hsrc :
      algebraMap ℂ (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) c =
        Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.C c) := by
    simpa only [Ideal.Quotient.mkₐ_eq_mk] using
      (Ideal.Quotient.mkₐ ℂ (vanishingIdeal A)).commutes c |>.symm
  have htgt :
      algebraMap ℂ (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) c =
        Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.C c) := by
    simpa only [Ideal.Quotient.mkₐ_eq_mk] using
      (Ideal.Quotient.mkₐ ℂ (chartVanishingIdeal A i)).commutes c |>.symm
  rw [hsrc, htgt]
  simp [quotientDehomogenize, dehomogenize]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeChartScalars
