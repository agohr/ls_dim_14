import QuaternionicSymmetry.ComplexExponentialIntegerKernel
import QuaternionicSymmetry.HolomorphicExponentialSheaf

/-! Locally constant integer periods are genuine holomorphic functions,
and exhaust the kernel of the actual holomorphic exponential on every open
set. This is the sectionwise exactness needed for the exponential sequence;
no Picard or cohomology comparison is assumed. -/

namespace QuaternionicSymmetry.HolomorphicIntegerPeriods

open TopologicalSpace Manifold
open HolomorphicLineModuleSheaf ComplexExponentialIntegerKernel
open scoped Manifold ContDiff Topology
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

def periodFunction {U : Opens B} (k : LocallyConstant U ℤ) : Functions IB U := by
  refine ⟨fun x => (k x : ℂ) * period, ?_⟩
  intro x
  apply contMDiffAt_const.congr_of_eventuallyEq
  filter_upwards [k.isLocallyConstant.eventually_eq x] with y hy
  exact congrArg (fun n : ℤ => (n : ℂ) * period) hy

theorem periodFunction_injective (U : Opens B) :
    Function.Injective (periodFunction IB (U := U)) := by
  intro k l h
  apply LocallyConstant.ext
  intro x
  exact integer_period_injective (congrArg (fun f : Functions IB U => f x) h)

theorem exp_periodFunction {U : Opens B} (k : LocallyConstant U ℤ) (x : U) :
    Complex.exp (periodFunction IB k x) = 1 := exp_integer_period (k x)

theorem exponential_kernel_iff {U : Opens B} (f : Functions IB U) :
    (∀ x, Complex.exp (f x) = 1) ↔
      ∃ k : LocallyConstant U ℤ, periodFunction IB k = f := by
  constructor
  · intro he
    obtain ⟨k, hk⟩ := exists_integer_period f.contMDiff.continuous he
    refine ⟨k, Subtype.ext ?_⟩
    funext x
    exact (hk x).symm
  · rintro ⟨k, rfl⟩
    exact exp_periodFunction IB k

end
end QuaternionicSymmetry.HolomorphicIntegerPeriods
