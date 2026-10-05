import QuaternionicSymmetry.ComplexProjectiveActualConeProjScheme

/-! The actual coordinate classes are homogeneous elements of degree one
in the genuine cone-quotient grading. They index the eventual standard
`Proj` opens; covering and chart-ring comparison are further lemmas. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjCoordinates

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
noncomputable section

variable {d : ℕ}

def coordinateClass (A : Set (Space d)) (i : Fin (d + 1)) :
    MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A :=
  Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.X i)

theorem coordinateClass_mem_degreeOne (A : Set (Space d))
    (i : Fin (d + 1)) :
    coordinateClass A i ∈ quotientPiece A 1 := by
  rw [mem_quotientPiece_iff]
  exact ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i, rfl⟩

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjCoordinates
