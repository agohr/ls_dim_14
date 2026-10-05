import QuaternionicSymmetry.LocalChernWeilLinear
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Trace

/-! The actual trace on finite-dimensional real endomorphisms gives a closed,
gauge-invariant curvature two-form. Changes of connection have an explicit
transgression one-form. No cyclicity assumption remains in these results. -/

namespace QuaternionicSymmetry.LocalEndomorphismTrace

open LocalConnection LocalConnectionForms LocalConnectionGauge LocalChernWeilLinear
  DifferentialFormCoefficient
open scoped Topology

noncomputable section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]

def traceCLM : (V →L[ℝ] V) →L[ℝ] ℝ :=
  ((LinearMap.trace ℝ V).comp
    (Module.End.toContinuousLinearMap (𝕜 := ℝ) V).symm.toLinearMap).toContinuousLinearMap

theorem traceCLM_apply (a : V →L[ℝ] V) :
    traceCLM a = LinearMap.trace ℝ V a.toLinearMap := rfl

theorem traceCLM_cyclic (a b : V →L[ℝ] V) : traceCLM (a * b) = traceCLM (b * a) :=
  LinearMap.trace_mul_comm ℝ a.toLinearMap b.toLinearMap

def traceCurvature (Γ : Form (E := E) (A := V →L[ℝ] V)) :
    E → E [⋀^Fin 2]→L[ℝ] ℝ := characteristicForm traceCLM Γ

theorem traceCurvature_closed (Γ : Form (E := E) (A := V →L[ℝ] V)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) : extDeriv (traceCurvature Γ) x = 0 :=
  closed traceCLM traceCLM_cyclic Γ x hΓ

theorem traceCurvature_transgression (Γ₀ Γ₁ : Form (E := E) (A := V →L[ℝ] V)) (x : E)
    (h₀ : DifferentiableAt ℝ Γ₀ x) (h₁ : DifferentiableAt ℝ Γ₁ x) :
    traceCurvature Γ₁ x - traceCurvature Γ₀ x =
      extDeriv (mapForm traceCLM (connectionForm (Γ₁ - Γ₀))) x :=
  transgression traceCLM traceCLM_cyclic Γ₀ Γ₁ x h₀ h₁

theorem traceCurvature_gauge_invariant (Γ : Form (E := E) (A := V →L[ℝ] V))
    (g h : E → V →L[ℝ] V) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1) (hright : g x * h x = 1) :
    traceCurvature (transform Γ g h) x = traceCurvature Γ x :=
  gauge_invariant traceCLM traceCLM_cyclic Γ g h x hΓ hg hh hleft hright

end
end QuaternionicSymmetry.LocalEndomorphismTrace
