import QuaternionicSymmetry.DifferentialFormCoefficient
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Finite polynomial time integrals commute with the local exterior derivative.
This is the integration step used in higher local Chern--Weil transgression. -/

namespace QuaternionicSymmetry.LocalPolynomialTransgressionIntegral

open scoped Topology

noncomputable section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] {p : ℕ}

local instance : NormedAddCommGroup (E [⋀^Fin p]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin p]→L[ℝ] B) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin (p + 1)]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin (p + 1)]→L[ℝ] B) := inferInstance

theorem integral_monomial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (k : ℕ) (a : V) :
    (∫ t in (0 : ℝ)..1, t ^ k • a) = (1 / (k + 1) : ℝ) • a := by
  rw [intervalIntegral.integral_smul_const, integral_pow]
  norm_num

theorem integral_polynomial (s : Finset ℕ) (A : ℕ → E [⋀^Fin p]→L[ℝ] B) :
    (∫ t in (0 : ℝ)..1, ∑ k ∈ s, t ^ k • A k) =
      ∑ k ∈ s, (1 / (k + 1) : ℝ) • A k := by
  rw [intervalIntegral.integral_finset_sum]
  · simp only [integral_monomial]
  · intro k hk
    exact ((continuous_id.pow k).smul continuous_const).intervalIntegrable 0 1

omit [CompleteSpace B] in
theorem extDeriv_finset_sum {ι : Type*} (s : Finset ι)
    (A : ι → E → E [⋀^Fin p]→L[ℝ] B) (x : E)
    (hA : ∀ k ∈ s, DifferentiableAt ℝ (A k) x) :
    extDeriv (fun y => ∑ k ∈ s, A k y) x =
      ∑ k ∈ s, extDeriv (A k) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext v
      simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  | @insert k s hks ih =>
      have hk : DifferentiableAt ℝ (A k) x := hA k (Finset.mem_insert_self k s)
      have hs : DifferentiableAt ℝ (fun y => ∑ j ∈ s, A j y) x := by
        apply DifferentiableAt.fun_sum
        intro j hj
        exact hA j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hks]
      rw [extDeriv_fun_add hk hs, ih]
      intro j hj
      exact hA j (Finset.mem_insert_of_mem hj)

/-- Spatial exterior differentiation commutes with the time integral of a
finite polynomial whose coefficient forms are differentiable at `x`. -/
theorem extDeriv_integral_polynomial (s : Finset ℕ)
    (A : ℕ → E → E [⋀^Fin p]→L[ℝ] B) (x : E)
    (hA : ∀ k ∈ s, DifferentiableAt ℝ (A k) x) :
    extDeriv (fun y => ∫ t in (0 : ℝ)..1,
      ∑ k ∈ s, t ^ k • A k y) x =
    ∫ t in (0 : ℝ)..1,
      extDeriv (fun y => ∑ k ∈ s, t ^ k • A k y) x := by
  have hleft : (fun y => ∫ t in (0 : ℝ)..1,
      ∑ k ∈ s, t ^ k • A k y) =
      (fun y => ∑ k ∈ s, (1 / (k + 1) : ℝ) • A k y) := by
    funext y
    exact integral_polynomial s (fun k => A k y)
  have hright (t : ℝ) :
      extDeriv (fun y => ∑ k ∈ s, t ^ k • A k y) x =
        ∑ k ∈ s, t ^ k • extDeriv (A k) x := by
    rw [extDeriv_finset_sum s (fun k y => t ^ k • A k y) x]
    · apply Finset.sum_congr rfl
      intro k hk
      change extDeriv (t ^ k • A k) x = _
      exact extDeriv_smul (t ^ k) (A k)
    · intro k hk
      exact (hA k hk).const_smul (t ^ k)
  simp only [hleft, hright]
  rw [integral_polynomial]
  rw [extDeriv_finset_sum s (fun k y => (1 / (k + 1) : ℝ) • A k y) x]
  · apply Finset.sum_congr rfl
    intro k hk
    change extDeriv ((1 / (k + 1) : ℝ) • A k) x = _
    exact extDeriv_smul (1 / (k + 1) : ℝ) (A k)
  · intro k hk
    change DifferentiableAt ℝ ((1 / (k + 1) : ℝ) • A k) x
    exact (hA k hk).const_smul _

/-- The index of a finite time polynomial need not equal its exponent.  In
particular, ordered curvature words can have duplicate exponents. -/
theorem integral_weighted_polynomial {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (s : Finset ι) (degree : ι → ℕ) (A : ι → V) :
    (∫ t in (0 : ℝ)..1, ∑ i ∈ s, t ^ degree i • A i) =
      ∑ i ∈ s, (1 / (degree i + 1) : ℝ) • A i := by
  rw [intervalIntegral.integral_finset_sum]
  · simp only [integral_monomial]
  · intro i hi
    exact ((continuous_id.pow (degree i)).smul continuous_const).intervalIntegrable 0 1

/-- Exterior differentiation commutes with time integration of a finite
polynomial with arbitrarily indexed monomials and differentiable coefficient
forms. -/
theorem extDeriv_integral_weighted_polynomial {ι : Type*}
    (s : Finset ι) (degree : ι → ℕ)
    (A : ι → E → E [⋀^Fin p]→L[ℝ] B) (x : E)
    (hA : ∀ i ∈ s, DifferentiableAt ℝ (A i) x) :
    extDeriv (fun y => ∫ t in (0 : ℝ)..1,
      ∑ i ∈ s, t ^ degree i • A i y) x =
    ∫ t in (0 : ℝ)..1,
      extDeriv (fun y => ∑ i ∈ s, t ^ degree i • A i y) x := by
  have hleft : (fun y => ∫ t in (0 : ℝ)..1,
      ∑ i ∈ s, t ^ degree i • A i y) =
      (fun y => ∑ i ∈ s, (1 / (degree i + 1) : ℝ) • A i y) := by
    funext y
    exact integral_weighted_polynomial s degree (fun i => A i y)
  have hright (t : ℝ) :
      extDeriv (fun y => ∑ i ∈ s, t ^ degree i • A i y) x =
        ∑ i ∈ s, t ^ degree i • extDeriv (A i) x := by
    rw [extDeriv_finset_sum s (fun i y => t ^ degree i • A i y) x]
    · apply Finset.sum_congr rfl
      intro i hi
      change extDeriv (t ^ degree i • A i) x = _
      exact extDeriv_smul (t ^ degree i) (A i)
    · intro i hi
      exact (hA i hi).const_smul (t ^ degree i)
  simp only [hleft, hright]
  rw [integral_weighted_polynomial]
  rw [extDeriv_finset_sum s
    (fun i y => (1 / (degree i + 1) : ℝ) • A i y) x]
  · apply Finset.sum_congr rfl
    intro i hi
    change extDeriv ((1 / (degree i + 1) : ℝ) • A i) x = _
    exact extDeriv_smul (1 / (degree i + 1) : ℝ) (A i)
  · intro i hi
    change DifferentiableAt ℝ ((1 / (degree i + 1) : ℝ) • A i) x
    exact (hA i hi).const_smul _

end
end QuaternionicSymmetry.LocalPolynomialTransgressionIntegral
