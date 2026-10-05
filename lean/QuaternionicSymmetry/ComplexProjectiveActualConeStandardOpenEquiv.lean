import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenInjective
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenSurjective

/-! The literal Mathlib degree-zero localization of the actual homogeneous
cone quotient at a coordinate is ring-isomorphic to the literal polynomial
coordinate ring of that actual affine chart locus. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenEquiv

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeStandardOpenMap
open ComplexProjectiveActualConeStandardOpenInjective
open ComplexProjectiveActualConeStandardOpenSurjective
noncomputable section

variable {d : ℕ}

def standardOpenEquiv (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) ≃+*
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact RingEquiv.ofBijective (standardOpenToChart A hA hNonempty i)
    ⟨standardOpenToChart_injective A hA hNonempty i,
      standardOpenToChart_surjective A hA hNonempty i⟩

theorem standardOpenEquiv_apply (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    ∀ x : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i),
      standardOpenEquiv A hA hNonempty i x =
        standardOpenToChart A hA hNonempty i x := by
  intro x
  rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenEquiv
