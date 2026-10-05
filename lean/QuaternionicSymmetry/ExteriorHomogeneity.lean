import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import QuaternionicSymmetry.CertificateHomogeneity
import QuaternionicSymmetry.ExteriorCertificates

/-!
  Weighted homogeneous universal polynomials evaluate to homogeneous exterior forms.

  Here weights `1,1,2,3,4` correspond to exterior degrees `4,4,8,12,16`.
  The evaluation is made in the proved commutative even subalgebra, while degree
  membership is proved after coercion to the ambient exterior algebra.
-/

namespace QuaternionicSymmetry
namespace ExteriorHomogeneity

open AlgebraCertificates CertificateHomogeneity ExteriorCertificates

noncomputable section

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]

private def inputsE
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) : Fin 5 → EvenForms.evenSubalgebra R V :=
  ![liftEven 2 u, liftEven 2 z₁, liftEven 4 z₂, liftEven 6 z₃, liftEven 8 z₄]

private def inputsA
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) : Fin 5 → ExteriorAlgebra R V :=
  fun i => (inputsE u z₁ z₂ z₃ z₄ i : ExteriorAlgebra R V)

omit [Algebra ℚ R] in
private theorem inputsA_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V)
    (i : Fin 5) :
    inputsA u z₁ z₂ z₃ z₄ i ∈ ExteriorAlgebra.exteriorPower R
      (4 * weights i) V := by
  fin_cases i
  · exact u.property
  · exact z₁.property
  · exact z₂.property
  · exact z₃.property
  · exact z₄.property

omit [Algebra ℚ R] in
private theorem scalar_mem (r : R) :
    algebraMap R (ExteriorAlgebra R V) r ∈ ExteriorAlgebra.exteriorPower R 0 V := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (ExteriorAlgebra.exteriorPower R 0 V).smul_mem r
    (SetLike.one_mem_graded _)

omit [Algebra ℚ R] in
private theorem prod_inputs_mem_aux
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V)
    (d : Fin 5 →₀ ℕ) (s : Finset (Fin 5)) :
    ((∏ i ∈ s, inputsE u z₁ z₂ z₃ z₄ i ^ d i : EvenForms.evenSubalgebra R V) :
      ExteriorAlgebra R V) ∈ ExteriorAlgebra.exteriorPower R
      (4 * ∑ i ∈ s, d i * weights i) V := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact SetLike.one_mem_graded (fun n : ℕ => ExteriorAlgebra.exteriorPower R n V)
  | insert i s his ih =>
      rw [Finset.prod_insert his, Finset.sum_insert his]
      have hi_mem : inputsA u z₁ z₂ z₃ z₄ i ^ d i ∈
          ExteriorAlgebra.exteriorPower R (4 * (d i * weights i)) V := by
        simpa [nsmul_eq_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          (SetLike.pow_mem_graded (d i) (inputsA_mem u z₁ z₂ z₃ z₄ i))
      have hmul := SetLike.mul_mem_graded hi_mem ih
      simpa only [map_mul, map_pow, Nat.mul_add] using hmul

omit [Algebra ℚ R] in
private theorem prod_inputs_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V)
    (d : Fin 5 →₀ ℕ) :
    ((d.prod fun i e => inputsE u z₁ z₂ z₃ z₄ i ^ e : EvenForms.evenSubalgebra R V) :
      ExteriorAlgebra R V) ∈ ExteriorAlgebra.exteriorPower R
      (4 * Finsupp.weight weights d) V := by
  change ((∏ i ∈ d.support, inputsE u z₁ z₂ z₃ z₄ i ^ d i : EvenForms.evenSubalgebra R V) :
      ExteriorAlgebra R V) ∈ ExteriorAlgebra.exteriorPower R
      (4 * Finsupp.weight weights d) V
  rw [Finsupp.weight_apply]
  simpa [Finsupp.sum, nsmul_eq_mul] using prod_inputs_mem_aux u z₁ z₂ z₃ z₄ d d.support

private theorem evaluateExterior_eq_aeval
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) (p : P) :
    evaluateExterior u z₁ z₂ z₃ z₄ p =
      ((MvPolynomial.aeval (inputsE u z₁ z₂ z₃ z₄) p : EvenForms.evenSubalgebra R V) :
        ExteriorAlgebra R V) := rfl

private theorem evaluateExterior_add
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) (p q : P) :
    evaluateExterior u z₁ z₂ z₃ z₄ (p + q) =
      evaluateExterior u z₁ z₂ z₃ z₄ p + evaluateExterior u z₁ z₂ z₃ z₄ q := by
  simp [evaluateExterior, evaluateEven]

private theorem eval_monomial_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V)
    (d : Fin 5 →₀ ℕ) (a : ℚ) :
    evaluateExterior u z₁ z₂ z₃ z₄ (MvPolynomial.monomial d a) ∈
      ExteriorAlgebra.exteriorPower R (4 * Finsupp.weight weights d) V := by
  rw [evaluateExterior_eq_aeval, MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial]
  have hs : ((algebraMap ℚ (EvenForms.evenSubalgebra R V) a : EvenForms.evenSubalgebra R V) :
      ExteriorAlgebra R V) = algebraMap R (ExteriorAlgebra R V) (algebraMap ℚ R a) := by
    rfl
  rw [show ((algebraMap ℚ (EvenForms.evenSubalgebra R V) a *
      d.prod (fun i e => inputsE u z₁ z₂ z₃ z₄ i ^ e) : EvenForms.evenSubalgebra R V) :
      ExteriorAlgebra R V) =
      ((algebraMap ℚ (EvenForms.evenSubalgebra R V) a : EvenForms.evenSubalgebra R V) :
        ExteriorAlgebra R V) *
      ((d.prod fun i e => inputsE u z₁ z₂ z₃ z₄ i ^ e : EvenForms.evenSubalgebra R V) :
        ExteriorAlgebra R V) by rfl]
  rw [hs]
  simpa using SetLike.mul_mem_graded (scalar_mem (algebraMap ℚ R a))
    (prod_inputs_mem u z₁ z₂ z₃ z₄ d)

/-- A weighted homogeneous universal polynomial evaluates to an exterior form of four times
its weighted degree. -/
theorem evaluateExterior_mem_of_WH
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V)
    {p : P} {n : ℕ} (hp : WH p n) :
    evaluateExterior u z₁ z₂ z₃ z₄ p ∈ ExteriorAlgebra.exteriorPower R (4 * n) V := by
  refine MvPolynomial.IsWeightedHomogeneous.induction_on
    (motive := fun q _ => evaluateExterior u z₁ z₂ z₃ z₄ q ∈
      ExteriorAlgebra.exteriorPower R (4 * n) V) ?_ ?_ ?_ hp
  · exact (ExteriorAlgebra.exteriorPower R (4 * n) V).zero_mem
  · intro p q hp hq ihp ihq
    rw [evaluateExterior_add]
    exact (ExteriorAlgebra.exteriorPower R (4 * n) V).add_mem ihp ihq
  · intro d a hd
    simpa only [hd] using eval_monomial_mem u z₁ z₂ z₃ z₄ d a

theorem K₂_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V) (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V) (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ K₂ ∈ ExteriorAlgebra.exteriorPower R 8 V := by
  simpa using evaluateExterior_mem_of_WH u z₁ z₂ z₃ z₄ K₂_wh

theorem K₃_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V) (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V) (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ K₃ ∈ ExteriorAlgebra.exteriorPower R 12 V := by
  simpa using evaluateExterior_mem_of_WH u z₁ z₂ z₃ z₄ K₃_wh

theorem K₄_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V) (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V) (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ K₄ ∈ ExteriorAlgebra.exteriorPower R 16 V := by
  simpa using evaluateExterior_mem_of_WH u z₁ z₂ z₃ z₄ K₄_wh

theorem K₅_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V) (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V) (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ K₅ ∈ ExteriorAlgebra.exteriorPower R 20 V := by
  simpa using evaluateExterior_mem_of_WH u z₁ z₂ z₃ z₄ K₅_wh

theorem K₆_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V) (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V) (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ K₆ ∈ ExteriorAlgebra.exteriorPower R 24 V := by
  simpa using evaluateExterior_mem_of_WH u z₁ z₂ z₃ z₄ K₆_wh

theorem K₇_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V) (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V) (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ K₇ ∈ ExteriorAlgebra.exteriorPower R 28 V := by
  simpa using evaluateExterior_mem_of_WH u z₁ z₂ z₃ z₄ K₇_wh

theorem K₈_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V) (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V) (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ K₈ ∈ ExteriorAlgebra.exteriorPower R 32 V := by
  simpa using evaluateExterior_mem_of_WH u z₁ z₂ z₃ z₄ K₈_wh

theorem K₉_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V) (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V) (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ K₉ ∈ ExteriorAlgebra.exteriorPower R 36 V := by
  simpa using evaluateExterior_mem_of_WH u z₁ z₂ z₃ z₄ K₉_wh

theorem K₁₀_mem
    (u : ExteriorAlgebra.exteriorPower R 4 V) (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V) (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ K₁₀ ∈ ExteriorAlgebra.exteriorPower R 40 V := by
  simpa using evaluateExterior_mem_of_WH u z₁ z₂ z₃ z₄ K₁₀_wh

end
end ExteriorHomogeneity
end QuaternionicSymmetry
