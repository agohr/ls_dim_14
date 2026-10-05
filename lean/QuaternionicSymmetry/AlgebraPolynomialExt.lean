import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-! Real scalar evaluations detect polynomials with coefficients in any real
algebra, including the commutative algebra of even exterior forms. -/

namespace QuaternionicSymmetry.AlgebraPolynomialExt

open scoped BigOperators

noncomputable section

variable {ι S : Type*} [Fintype ι] [CommRing S] [Algebra ℝ S]

def mapCoefficients (L : S →ₗ[ℝ] ℝ) : MvPolynomial ι S →ₗ[ℝ] MvPolynomial ι ℝ :=
  Finsupp.mapRange.linearMap L

omit [Fintype ι] in
@[simp] theorem mapCoefficients_monomial (L : S →ₗ[ℝ] ℝ) (d : ι →₀ ℕ) (c : S) :
    mapCoefficients L (MvPolynomial.monomial d c) = MvPolynomial.monomial d (L c) := by
  exact Finsupp.mapRange_single (hf := L.map_zero)

omit [Fintype ι] in
@[simp] theorem coeff_mapCoefficients (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial ι S)
    (d : ι →₀ ℕ) : MvPolynomial.coeff d (mapCoefficients L p) = L (MvPolynomial.coeff d p) := rfl

theorem eval_mapCoefficients (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial ι S) (x : ι → ℝ) :
    MvPolynomial.eval x (mapCoefficients L p) =
      L (MvPolynomial.eval (fun i => algebraMap ℝ S (x i)) p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      simp only [mapCoefficients_monomial, MvPolynomial.eval_monomial, Finsupp.prod_pow]
      simp only [← map_pow, ← map_prod]
      rw [mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem mvPolynomial_ext {p q : MvPolynomial ι S}
    (h : ∀ x : ι → ℝ,
      MvPolynomial.eval (fun i => algebraMap ℝ S (x i)) p =
        MvPolynomial.eval (fun i => algebraMap ℝ S (x i)) q) : p = q := by
  ext d
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ _).mp
  intro L
  have hL : mapCoefficients L p = mapCoefficients L q := by
    apply MvPolynomial.funext
    intro x
    rw [eval_mapCoefficients, eval_mapCoefficients, h x]
  have hc := congrArg (MvPolynomial.coeff d) hL
  simpa only [coeff_mapCoefficients, map_sub, sub_eq_zero] using hc

theorem polynomial_ext {p q : Polynomial S}
    (h : ∀ x : ℝ, p.eval (algebraMap ℝ S x) = q.eval (algebraMap ℝ S x)) : p = q := by
  apply (MvPolynomial.pUnitAlgEquiv S).symm.injective
  apply mvPolynomial_ext
  intro x
  change MvPolynomial.eval₂ (RingHom.id S) (fun i => algebraMap ℝ S (x i))
      ((MvPolynomial.pUnitAlgEquiv S).symm p) =
    MvPolynomial.eval₂ (RingHom.id S) (fun i => algebraMap ℝ S (x i))
      ((MvPolynomial.pUnitAlgEquiv S).symm q)
  rw [MvPolynomial.eval₂_pUnitAlgEquiv_symm, MvPolynomial.eval₂_pUnitAlgEquiv_symm]
  exact h (x ())

end
end QuaternionicSymmetry.AlgebraPolynomialExt
