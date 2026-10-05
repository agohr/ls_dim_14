import QuaternionicSymmetry.ComplexProjectiveActualConeProjCoordinateIdeal

/-! The actual degree-one coordinate basic opens cover the literal
`Proj` of the homogeneous cone quotient. This provides a finite affine
cover for subsequent localization maps and gluing. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjCoordinateCover

open AlgebraicGeometry ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjCoordinateIdeal
noncomputable section

variable {d : ℕ}

theorem irrelevant_le_coordinateIdeal (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    (letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    (HomogeneousIdeal.irrelevant (quotientPiece A)).toIdeal) ≤
      coordinateIdeal A := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  rw [HomogeneousIdeal.irrelevant_eq_span]
  apply Ideal.span_le.mpr
  intro q hq
  obtain ⟨s, hs, hqs⟩ := hq
  obtain ⟨n, rfl⟩ := hs
  obtain ⟨t, ht, hqt⟩ := hqs
  obtain ⟨hn, rfl⟩ := ht
  exact quotientPiece_positive_le_coordinateIdeal A hn hqt

theorem coordinate_basicOpens_cover (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    (letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    (⨆ i : Fin (d + 1),
      Proj.basicOpen (quotientPiece A) (coordinateClass A i))) = ⊤ := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  exact Proj.iSup_basicOpen_eq_top (quotientPiece A) (coordinateClass A)
    (irrelevant_le_coordinateIdeal A hA hNonempty)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjCoordinateCover
