import QuaternionicSymmetry.ComplexProjectiveActualConeProjChartIso

/-! Canonical complex scalars in degree zero of the actual homogeneous
cone quotient, prerequisite for a single global `Spec ℂ` structure. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDegreeZeroScalars

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
noncomputable section

variable {d : ℕ}

def scalarToDegreeZero (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    ℂ →+* quotientPiece A 0 := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact (GradedRing.projZeroRingHom' (quotientPiece A)).comp
    (algebraMap ℂ (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A))

theorem scalar_mem_degreeZero (A : Set (Space d)) (c : ℂ) :
    algebraMap ℂ (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) c ∈
      quotientPiece A 0 := by
  rw [mem_quotientPiece_iff]
  exact ⟨MvPolynomial.C c,
    MvPolynomial.isHomogeneous_C (Fin (d + 1)) c, by
      simpa only [Ideal.Quotient.mkₐ_eq_mk] using
        (Ideal.Quotient.mkₐ ℂ (vanishingIdeal A)).commutes c⟩

theorem scalarToDegreeZero_coe (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (c : ℂ) :
    ((scalarToDegreeZero A hA hNonempty c : quotientPiece A 0) :
      MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) =
      algebraMap ℂ (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) c := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let q := algebraMap ℂ (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) c
  have hq : q ∈ quotientPiece A 0 := scalar_mem_degreeZero A c
  change ((GradedRing.projZeroRingHom' (quotientPiece A)) q :
    MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) = q
  conv_rhs => rw [← show (⟨q, hq⟩ : quotientPiece A 0).1 = q from rfl]
  rw [← GradedRing.projZeroRingHom'_apply_coe (quotientPiece A) ⟨q, hq⟩]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDegreeZeroScalars
