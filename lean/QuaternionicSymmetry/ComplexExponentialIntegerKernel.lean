import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.LocallyConstant.Basic

/-! The kernel of the actual complex exponential on continuous functions
is exactly the locally constant integer multiples of `2πi`. Local constancy
is proved using the inverse function theorem, not assumed from pointwise
membership in the period lattice. -/

namespace QuaternionicSymmetry.ComplexExponentialIntegerKernel

open Filter
open scoped Topology
noncomputable section

def period : ℂ := 2 * Real.pi * Complex.I

theorem period_ne_zero : period ≠ 0 := by
  unfold period
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

theorem integer_period_injective : Function.Injective
    (fun n : ℤ => (n : ℂ) * period) := by
  intro m n h
  have hcast : (m : ℂ) = (n : ℂ) := mul_right_cancel₀ period_ne_zero h
  exact_mod_cast hcast

variable {X : Type*} [TopologicalSpace X]

theorem isLocallyConstant_of_exp_eq_one {f : X → ℂ}
    (hf : Continuous f) (he : ∀ x, Complex.exp (f x) = 1) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let g := HasStrictDerivAt.localInverse Complex.exp (Complex.exp (f x))
    (f x) (Complex.hasStrictDerivAt_exp (f x)) (Complex.exp_ne_zero (f x))
  have hnear : ∀ᶠ z in 𝓝 (f x), g (Complex.exp z) = z :=
    (Complex.hasStrictDerivAt_exp (f x)).eventually_left_inverse
      (Complex.exp_ne_zero (f x))
  have hx : g (Complex.exp (f x)) = f x := hnear.self_of_nhds
  filter_upwards [hf.continuousAt.eventually hnear] with y hy
  calc
    f y = g (Complex.exp (f y)) := hy.symm
    _ = g (Complex.exp (f x)) := by rw [he y, he x]
    _ = f x := hx

/-- A continuous exponential-kernel section has one globally defined
locally constant integer section, with the exact analytic period. -/
theorem exists_integer_period {f : X → ℂ} (hf : Continuous f)
    (he : ∀ x, Complex.exp (f x) = 1) :
    ∃ k : LocallyConstant X ℤ, ∀ x, f x = (k x : ℂ) * period := by
  choose k hk using fun x => Complex.exp_eq_one_iff.mp (he x)
  have hk' : ∀ x, f x = (k x : ℂ) * period := hk
  have hlocal : IsLocallyConstant k := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [(isLocallyConstant_of_exp_eq_one hf he).eventually_eq x] with y hy
    exact integer_period_injective ((hk' y).symm.trans (hy.trans (hk' x)))
  exact ⟨⟨k, hlocal⟩, hk'⟩

theorem exp_integer_period (n : ℤ) : Complex.exp ((n : ℂ) * period) = 1 :=
  Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩

end
end QuaternionicSymmetry.ComplexExponentialIntegerKernel
