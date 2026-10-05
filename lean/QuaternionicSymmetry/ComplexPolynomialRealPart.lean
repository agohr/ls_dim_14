import QuaternionicSymmetry.Complexification
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! Coefficientwise real part commutes with polynomial evaluation at real
coefficients, including evaluation in a complexified real algebra. -/

namespace QuaternionicSymmetry.ComplexPolynomialRealPart

open scoped TensorProduct

noncomputable section

variable {β : Type*}

def realCoefficients : MvPolynomial β ℂ →ₗ[ℝ] MvPolynomial β ℝ :=
  Finsupp.mapRange.linearMap Complex.reLm

@[simp] theorem realCoefficients_monomial (d : β →₀ ℕ) (z : ℂ) :
    realCoefficients (MvPolynomial.monomial d z) = MvPolynomial.monomial d z.re := by
  exact Finsupp.mapRange_single (hf := Complex.reLm.map_zero)

theorem eval_realCoefficients (p : MvPolynomial β ℂ) (x : β → ℝ) :
    (realCoefficients p).eval x = (p.eval (fun i => (x i : ℂ))).re := by
  induction p using MvPolynomial.induction_on' with
  | monomial d z =>
    rw [realCoefficients_monomial]
    simp only [MvPolynomial.eval_monomial]
    have hprod : d.prod (fun i m => (x i : ℂ) ^ m) =
        (d.prod (fun i m => x i ^ m) : ℝ) := by
      simp [Finsupp.prod]
    rw [hprod]
    simp
  | add p q hp hq => simp [hp, hq]

variable {S : Type*} [CommRing S] [Algebra ℝ S]

/-- The polynomial is evaluated with complex coefficients in the left tensor
factor and real-algebra variables in the right factor. -/
def complexifiedEvaluation (η : β → S) : MvPolynomial β ℂ →+* ℂ ⊗[ℝ] S :=
  MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeLeft : ℂ →ₐ[ℝ] ℂ ⊗[ℝ] S).toRingHom
    (fun i => (Algebra.TensorProduct.includeRight : S →ₐ[ℝ] ℂ ⊗[ℝ] S) (η i))

theorem aeval_realCoefficients (p : MvPolynomial β ℂ) (η : β → S) :
    MvPolynomial.aeval η (realCoefficients p) =
      Complexification.realPart (complexifiedEvaluation η p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d z =>
    rw [realCoefficients_monomial]
    simp only [MvPolynomial.aeval_monomial, complexifiedEvaluation,
      MvPolynomial.eval₂Hom_monomial]
    have hprod : d.prod (fun i m =>
        (Algebra.TensorProduct.includeRight (η i) : ℂ ⊗[ℝ] S) ^ m) =
        Algebra.TensorProduct.includeRight (d.prod (fun i m => η i ^ m)) := by
      simp [Finsupp.prod]
    rw [hprod]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      Complexification.realPart_tmul, Algebra.smul_def]
  | add p q hp hq => simp [hp, hq]

end
end QuaternionicSymmetry.ComplexPolynomialRealPart
