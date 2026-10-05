import QuaternionicSymmetry.TorusIntegralCocharacter
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Max

/-! A finite family of integral weights admits an integral cocharacter
separating every pair of distinct weights. The proof uses ordinary integer
polynomials and their finite root sets, with no genericity source premise. -/
namespace QuaternionicSymmetry.TorusIntegralGenericCocharacter

open TorusIntegralCocharacter
open scoped BigOperators
noncomputable section

private def weightPolynomial {r : ℕ} (μ : Fin r → ℤ) : Polynomial ℤ :=
  ∑ i : Fin r, Polynomial.monomial i.val (μ i)

private theorem weightPolynomial_coeff {r : ℕ} (μ : Fin r → ℤ) (i : Fin r) :
    (weightPolynomial μ).coeff i.val = μ i := by
  classical
  simp [weightPolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
    Fin.val_inj]

private theorem weightPolynomial_injective {r : ℕ} :
    Function.Injective (weightPolynomial (r := r)) := by
  intro μ ν h
  funext i
  have hi := congrArg (fun p : Polynomial ℤ => p.coeff i.val) h
  simpa only [weightPolynomial_coeff] using hi

private theorem weightPolynomial_eval {r : ℕ} (μ : Fin r → ℤ) (t : ℤ) :
    (weightPolynomial μ).eval t = pairing μ (fun i => t ^ i.val) := by
  simp [weightPolynomial, pairing, Polynomial.eval_finset_sum]

theorem exists_separating_cocharacter {r : ℕ} {ι : Type*} [Fintype ι]
    (μ : ι → Fin r → ℤ) :
    ∃ u : Fin r → ℤ, ∀ i j, pairing (μ i) u = pairing (μ j) u → μ i = μ j := by
  classical
  let Pairs := {p : ι × ι // μ p.1 ≠ μ p.2}
  let p : Pairs → Polynomial ℤ :=
    fun ij => weightPolynomial (μ ij.1.1) - weightPolynomial (μ ij.1.2)
  have hp : ∀ ij : Pairs, p ij ≠ 0 := by
    intro ij hz
    exact ij.2 (weightPolynomial_injective (sub_eq_zero.mp hz))
  let P : Polynomial ℤ := ∏ ij : Pairs, p ij
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun ij _ => hp ij)
  have ht : ∃ t : ℤ, P.eval t ≠ 0 := by
    by_contra! hn
    apply hP
    apply Polynomial.funext
    intro t
    simpa using hn t
  obtain ⟨t,ht⟩ := ht
  refine ⟨fun i => t ^ i.val, ?_⟩
  intro i j hij
  by_contra hne
  have hpij : (p (⟨(i,j),hne⟩ : Pairs)).eval t ≠ 0 := by
    have hprod : (∏ ij : Pairs, (p ij).eval t) ≠ 0 := by
      simpa [P, Polynomial.eval_prod] using ht
    exact Finset.prod_ne_zero_iff.mp hprod _ (Finset.mem_univ _)
  apply hpij
  change (weightPolynomial (μ i) - weightPolynomial (μ j)).eval t = 0
  rw [Polynomial.eval_sub, weightPolynomial_eval, weightPolynomial_eval, hij, sub_self]

theorem exists_exposed_minimum {r : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : ι → Fin r → ℤ) :
    ∃ (j : ι) (u : Fin r → ℤ),
      (∀ i, pairing (μ j) u ≤ pairing (μ i) u) ∧
      ∀ i, pairing (μ i) u = pairing (μ j) u → μ i = μ j := by
  obtain ⟨u,hu⟩ := exists_separating_cocharacter μ
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ
    (fun i => pairing (μ i) u) Finset.univ_nonempty
  exact ⟨j,u,fun i => hj i (Finset.mem_univ i),fun i hi => hu i j hi⟩

end
end QuaternionicSymmetry.TorusIntegralGenericCocharacter
