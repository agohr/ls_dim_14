import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPointComap
import QuaternionicSymmetry.ComplexProjectiveActualConeProjCoordinates

/-! The actual quotient-Proj point of a classical projective line belongs to
exactly those standard affine opens whose corresponding coordinate is nonzero. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPointChart

open AlgebraicGeometry ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeClassicalPoint
open ComplexProjectiveLineProjPoint
noncomputable section

variable {d : ℕ}

theorem classicalPoint_mem_basicOpen_iff (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (x : A) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA ⟨x.1, x.2⟩
    classicalPointToActualProj A hA x ∈
      Proj.basicOpen (quotientPiece A) (coordinateClass A i) ↔
      x.1.rep i ≠ 0 := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA ⟨x.1, x.2⟩
  rw [Proj.mem_basicOpen]
  change ¬ coordinateClass A i ∈
    (quotientLinePrime A x.1 x.2).homogeneousCore (quotientPiece A) ↔ _
  constructor
  · intro h hi
    apply h
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (show SetLike.IsHomogeneousElem (quotientPiece A) (coordinateClass A i) from
        ⟨1, coordinateClass_mem_degreeOne A i⟩)
    change quotientLineEval A x.1 x.2 (coordinateClass A i) = 0
    simp [coordinateClass, quotientLineEval, lineEval, hi]
  · intro hi h
    have hker : coordinateClass A i ∈ quotientLinePrime A x.1 x.2 :=
      (Ideal.toIdeal_homogeneousCore_le
        (𝒜 := quotientPiece A) (I := quotientLinePrime A x.1 x.2)) h
    have heval : quotientLineEval A x.1 x.2 (coordinateClass A i) = 0 :=
      (RingHom.mem_ker).mp hker
    simp [coordinateClass, quotientLineEval, lineEval, hi] at heval

end
end QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPointChart
