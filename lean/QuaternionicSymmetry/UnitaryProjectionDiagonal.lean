import QuaternionicSymmetry.UnitaryColumnMoments
import QuaternionicSymmetry.UnitaryProjection
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Diagonal entries of Haar projections: their exact marginal moments,
constant sum, and exchangeability under coordinate permutations. -/

namespace QuaternionicSymmetry.UnitaryProjectionDiagonal

open Matrix MeasureTheory
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def entry (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) (i : κ) : ℝ :=
  ∑ a ∈ s, ‖(U : Matrix κ κ ℂ) i a‖ ^ 2

theorem entry_eq_re (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) (i : κ) :
    entry s U i = (UnitaryProjection.projection s U i i).re := by
  simp only [UnitaryProjection.projection_apply, entry, Complex.re_sum,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem sum_entry (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) :
    ∑ i, entry s U i = (s.card : ℝ) := by
  simp_rw [entry_eq_re]
  rw [← Complex.re_sum]
  change (Matrix.trace (UnitaryProjection.projection s U)).re = _
  rw [UnitaryProjection.trace_projection]
  simp

theorem continuous_entry (s : Finset κ) (i : κ) :
    Continuous (fun U : Matrix.unitaryGroup κ ℂ => entry s U i) := by
  unfold entry
  apply continuous_finset_sum
  intro a _
  exact (((continuous_apply a).comp
    ((continuous_apply i).comp continuous_subtype_val)).norm).pow 2

theorem continuous_integrable {f : Matrix.unitaryGroup κ ℂ → ℝ} (h : Continuous f) :
    Integrable f UnitaryHaarMeasure.probability :=
  integrableOn_univ.mp (h.continuousOn.integrableOn_compact isCompact_univ)

theorem entry_pow_integrable (s : Finset κ) (i : κ) (k : ℕ) :
    Integrable (fun U : Matrix.unitaryGroup κ ℂ => entry s U i ^ k)
      UnitaryHaarMeasure.probability :=
  continuous_integrable ((continuous_entry s i).pow k)

theorem integral_entry_power (s : Finset κ) (i : κ) (k : ℕ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ k ∂UnitaryHaarMeasure.probability) =
      ComplexGaussianPolynomial.expectation
        (ComplexGaussianLinearMoments.linearPolynomial
          (fun a : κ => if a ∈ s then (1 : ℝ) else 0) ^ k) /
          ((Fintype.card κ).ascFactorial k : ℝ) := by
  simpa [entry] using UnitaryColumnMoments.integral_row_weighted_power
    (fun a : κ => if a ∈ s then (1 : ℝ) else 0) k i

theorem integral_entry (s : Finset κ) (i : κ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ∂UnitaryHaarMeasure.probability) =
      (s.card : ℝ) / Fintype.card κ := by
  simpa [ComplexGaussianLinearMoments.expectation_linear, Nat.ascFactorial_succ] using
    integral_entry_power s i 1

theorem integral_entry_sq (s : Finset κ) (i : κ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ 2 ∂UnitaryHaarMeasure.probability) =
      (s.card : ℝ) * (s.card + 1) /
        ((Fintype.card κ : ℝ) * (Fintype.card κ + 1)) := by
  rw [integral_entry_power, ComplexGaussianLinearMoments.expectation_linear_sq]
  simp only [ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  push_cast
  congr 1 <;> ring

theorem integral_entry_cube (s : Finset κ) (i : κ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ 3 ∂UnitaryHaarMeasure.probability) =
      (s.card : ℝ) * (s.card + 1) * (s.card + 2) /
        ((Fintype.card κ : ℝ) * (Fintype.card κ + 1) * (Fintype.card κ + 2)) := by
  rw [integral_entry_power, ComplexGaussianLinearMoments.expectation_linear_cube]
  simp only [ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter,
    Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  push_cast
  congr 1 <;> ring

def permutation (e : Equiv.Perm κ) : Matrix.unitaryGroup κ ℂ :=
  ⟨e.permMatrix ℂ, Matrix.mem_unitaryGroup_iff.mpr (by
    change e.permMatrix ℂ * (e.permMatrix ℂ).conjTranspose = 1
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp)⟩

theorem permutation_mul_apply (e : Equiv.Perm κ) (U : Matrix.unitaryGroup κ ℂ)
    (i a : κ) :
    ((permutation e * U : Matrix.unitaryGroup κ ℂ) : Matrix κ κ ℂ) i a =
      (U : Matrix κ κ ℂ) (e i) a := by
  change (e.permMatrix ℂ * (U : Matrix κ κ ℂ)) i a = _
  change (e.permMatrix ℂ *ᵥ fun j => (U : Matrix κ κ ℂ) j a) i = _
  rw [Matrix.permMatrix_mulVec]
  rfl

theorem entry_permutation (s : Finset κ) (e : Equiv.Perm κ)
    (U : Matrix.unitaryGroup κ ℂ) (i : κ) :
    entry s (permutation e * U) i = entry s U (e i) := by
  simp only [entry, permutation_mul_apply]

theorem integral_permute (s : Finset κ) (e : Equiv.Perm κ) (f : (κ → ℝ) → ℝ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, f (fun i => entry s U (e i))
        ∂UnitaryHaarMeasure.probability) =
      ∫ U : Matrix.unitaryGroup κ ℂ, f (entry s U) ∂UnitaryHaarMeasure.probability := by
  have he (U : Matrix.unitaryGroup κ ℂ) :
      (fun i => entry s U (e i)) = entry s (permutation e * U) := by
    funext i
    exact (entry_permutation s e U i).symm
  simp_rw [he]
  exact UnitaryHaarMeasure.integral_mul_left (fun U => f (entry s U)) (permutation e)

end
end QuaternionicSymmetry.UnitaryProjectionDiagonal
