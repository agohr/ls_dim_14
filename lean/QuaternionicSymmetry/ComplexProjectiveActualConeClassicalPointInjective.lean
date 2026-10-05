import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPointChart
import QuaternionicSymmetry.ComplexProjectiveLineProjInjective

/-! Distinct classical points of the homogeneous projective cutout give
distinct points of its actual quotient Proj. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPointInjective

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeClassicalPoint
open ComplexProjectiveLineProjPoint ComplexProjectiveLineProjLocus
open ComplexProjectiveLineProjInjective
open scoped LinearAlgebra.Projectivization Polynomial
noncomputable section

variable {d : ℕ}

def classicalPointToActualProjFixed (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) (x : A) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    ProjectiveSpectrum (quotientPiece A) :=
  classicalPointToActualProj A hA x

theorem classicalPointToActualProj_injective (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    Function.Injective (classicalPointToActualProjFixed A hA hNonempty) := by
  intro x y hxy
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA ⟨x.1, x.2⟩
  have hcore : quotientLineHomogeneousPrime A hA x.1 x.2 =
      quotientLineHomogeneousPrime A hA y.1 y.2 :=
    congrArg ProjectiveSpectrum.asHomogeneousIdeal hxy
  have hj : ∃ j : Fin (d + 1), y.1.rep j ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply y.1.rep_nonzero
    funext i
    exact hno i
  obtain ⟨j, hj⟩ := hj
  have hlin (i : Fin (d + 1)) :
      y.1.rep j * x.1.rep i = y.1.rep i * x.1.rep j := by
    let p := lineEquation y.1.rep i j
    have hmemY : Ideal.Quotient.mk (vanishingIdeal A) p ∈
        quotientLineHomogeneousPrime A hA y.1 y.2 := by
      apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
        (𝒜 := quotientPiece A)
        (show SetLike.IsHomogeneousElem (quotientPiece A)
          (Ideal.Quotient.mk (vanishingIdeal A) p) from
          ⟨1, (mem_quotientPiece_iff A 1 _).mpr
            ⟨p, lineEquation_isHomogeneous y.1.rep i j, rfl⟩⟩)
      change quotientLineEval A y.1 y.2
        (Ideal.Quotient.mk (vanishingIdeal A) p) = 0
      rw [quotientLineEval_mk]
      simp [p, lineEval, lineEquation]
      ring
    have hmemX : Ideal.Quotient.mk (vanishingIdeal A) p ∈
        quotientLineHomogeneousPrime A hA x.1 x.2 := by
      rw [hcore]
      exact hmemY
    have hker : Ideal.Quotient.mk (vanishingIdeal A) p ∈
        quotientLinePrime A x.1 x.2 :=
      (Ideal.toIdeal_homogeneousCore_le
        (𝒜 := quotientPiece A) (I := quotientLinePrime A x.1 x.2)) hmemX
    have heval : MvPolynomial.eval x.1.rep p = 0 := by
      have h := (RingHom.mem_ker).mp hker
      have h' := congrArg (Polynomial.eval 1) h
      simpa [quotientLineEval_mk, eval_lineEval] using h'
    rw [lineEquation_eval] at heval
    exact sub_eq_zero.mp heval
  have hscale : (x.1.rep j / y.1.rep j) • y.1.rep = x.1.rep := by
    funext i
    change x.1.rep j / y.1.rep j * y.1.rep i = x.1.rep i
    have h := hlin i
    field_simp [hj]
    linear_combination -h
  have hpoints : (x.1 : Space d) = y.1 := by
    calc
      x.1 = Projectivization.mk ℂ x.1.rep x.1.rep_nonzero := x.1.mk_rep.symm
      _ = Projectivization.mk ℂ y.1.rep y.1.rep_nonzero :=
        (Projectivization.mk_eq_mk_iff' ℂ _ _ x.1.rep_nonzero y.1.rep_nonzero).mpr
          ⟨x.1.rep j / y.1.rep j, hscale⟩
      _ = y.1 := y.1.mk_rep
  exact Subtype.ext hpoints

end
end QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPointInjective
