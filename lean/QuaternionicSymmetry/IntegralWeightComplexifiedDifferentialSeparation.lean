import QuaternionicSymmetry.IntegralWeightRealSpanComplexSeparation
import QuaternionicSymmetry.RealToComplexTangentComplexificationLinear
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Literal coordinate values of integral-character differentials imply
separation after scalar extension from `ℝ` to `ℂ`, provided the integral
weight vectors span the real coordinate space. No geometric spanning claim
is made here. -/

namespace QuaternionicSymmetry.IntegralWeightComplexifiedDifferentialSeparation

open IntegralWeightRealSpanComplexSeparation
open RealToComplexTangentComplexification
open scoped TensorProduct
noncomputable section

variable {r : ℕ} {ι E : Type*} [AddCommGroup E] [Module ℝ E]

private def weightDotLinear (μ : Fin r → ℤ) :
    (Fin r → ℂ) →ₗ[ℂ] ℂ :=
  Fintype.linearCombination ℂ (fun j => (μ j : ℂ))

private theorem weightDotLinear_apply (μ : Fin r → ℤ) (z : Fin r → ℂ) :
    weightDotLinear μ z = complexWeightDot μ z := by
  simp only [weightDotLinear, Fintype.linearCombination_apply,
    complexWeightDot]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem complexified_differentials_separate_of_real_span
    (μ : ι → Fin r → ℤ)
    (bR : Module.Basis (Fin r) ℝ E)
    (β : ι → E →ₗ[ℝ] ℂ)
    (hCoord : ∀ i j, β i (bR j) = Complex.I * (μ i j : ℂ))
    (hSpan : Submodule.span ℝ
      (Set.range (fun i => realWeightVector (μ i))) = ⊤)
    (t : ℂ ⊗[ℝ] E)
    (ht : ∀ i, complexifiedMapComplex (β i) t = 0) : t = 0 := by
  classical
  let b : Module.Basis (Fin r) ℂ (ℂ ⊗[ℝ] E) := bR.baseChange ℂ
  let z : Fin r → ℂ := b.equivFun t
  have hFormula (i : ι) :
      complexifiedMapComplex (β i) t =
        Complex.I * complexWeightDot (μ i) z := by
    have hMap : complexifiedMapComplex (β i) =
        (Complex.I • weightDotLinear (μ i)).comp b.equivFun.toLinearMap := by
      apply b.ext
      intro j
      have hb : b j = (1 : ℂ) ⊗ₜ[ℝ] bR j := by simp [b]
      calc
        complexifiedMapComplex (β i) (b j) =
            Complex.I * (μ i j : ℂ) := by rw [hb]; simpa using hCoord i j
        _ = ((Complex.I • weightDotLinear (μ i)).comp
              b.equivFun.toLinearMap) (b j) := by
            simp [weightDotLinear, Fintype.linearCombination_apply,
              Finsupp.single_apply]
    rw [hMap]
    simp [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
      weightDotLinear_apply, z]
  have hz : ∀ i, complexWeightDot (μ i) z = 0 := by
    intro i
    have hi := hFormula i
    rw [ht i] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left Complex.I_ne_zero
  have hz0 := complexWeightDot_separates_of_real_span μ hSpan z hz
  apply b.equivFun.injective
  exact hz0

end
end QuaternionicSymmetry.IntegralWeightComplexifiedDifferentialSeparation
