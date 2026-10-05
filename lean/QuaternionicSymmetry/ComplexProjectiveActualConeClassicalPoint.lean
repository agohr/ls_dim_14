import QuaternionicSymmetry.ComplexProjectiveLineProjLocus
import QuaternionicSymmetry.ComplexProjectiveConeQuotientGrading

/-! A point of the literal homogeneous cutout defines a relevant homogeneous
prime in the *quotient* coordinate ring, hence a point of its actual Proj. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPoint

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveLineProjPoint ComplexProjectiveLineProjLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open scoped LinearAlgebra.Projectivization Polynomial
noncomputable section

variable {d : ℕ}

def quotientLineEval (A : Set (Space d)) (x : Space d) (hx : x ∈ A) :
    (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) →ₐ[ℂ] Polynomial ℂ :=
  Ideal.Quotient.liftₐ (vanishingIdeal A) (lineEval x.rep)
    (fun _ hp => (RingHom.mem_ker).mp
      (vanishingIdeal_le_linePrimeIdeal A x hx hp))

@[simp] theorem quotientLineEval_mk (A : Set (Space d))
    (x : Space d) (hx : x ∈ A)
    (p : MvPolynomial (Fin (d + 1)) ℂ) :
    quotientLineEval A x hx (Ideal.Quotient.mk (vanishingIdeal A) p) =
      lineEval x.rep p := by
  rfl

def quotientLinePrime (A : Set (Space d)) (x : Space d) (hx : x ∈ A) :
    Ideal (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) :=
  RingHom.ker (quotientLineEval A x hx).toRingHom

def quotientLineHomogeneousPrime (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (x : Space d) (hx : x ∈ A) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA ⟨x, hx⟩
    HomogeneousIdeal (quotientPiece A) :=
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA ⟨x, hx⟩
  (quotientLinePrime A x hx).homogeneousCore _

theorem quotientLineHomogeneousPrime_isPrime (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (x : Space d) (hx : x ∈ A) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA ⟨x, hx⟩
    (quotientLineHomogeneousPrime A hA x hx).toIdeal.IsPrime := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA ⟨x, hx⟩
  exact (RingHom.ker_isPrime (quotientLineEval A x hx).toRingHom).homogeneousCore

theorem quotientLineHomogeneousPrime_relevant (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (x : Space d) (hx : x ∈ A) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA ⟨x, hx⟩
    ¬ HomogeneousIdeal.irrelevant (quotientPiece A) ≤
      quotientLineHomogeneousPrime A hA x hx := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA ⟨x, hx⟩
  intro h
  have hi : ∃ i : Fin (d + 1), x.rep i ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply x.rep_nonzero
    funext i
    exact hno i
  obtain ⟨i, hi⟩ := hi
  have hX : Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.X i) ∈
      HomogeneousIdeal.irrelevant (quotientPiece A) :=
    HomogeneousIdeal.mem_irrelevant_of_mem (quotientPiece A)
      (show 0 < (1 : ℕ) by norm_num)
      (by
        change Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.X i) ∈
          quotientPiece A 1
        exact (mem_quotientPiece_iff A 1 _).mpr
          ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i, rfl⟩)
  have hker : Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.X i) ∈
      quotientLinePrime A x hx :=
    (Ideal.toIdeal_homogeneousCore_le
      (𝒜 := quotientPiece A) (I := quotientLinePrime A x hx)) (h hX)
  have heval : quotientLineEval A x hx
      (Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.X i)) = 0 :=
    (RingHom.mem_ker).mp hker
  simp [quotientLineEval, lineEval, hi] at heval

def classicalPointToActualProj (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (x : A) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA ⟨x.1, x.2⟩
    ProjectiveSpectrum (quotientPiece A) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA ⟨x.1, x.2⟩
  exact ⟨quotientLineHomogeneousPrime A hA x.1 x.2,
    quotientLineHomogeneousPrime_isPrime A hA x.1 x.2,
    quotientLineHomogeneousPrime_relevant A hA x.1 x.2⟩

end
end QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPoint
