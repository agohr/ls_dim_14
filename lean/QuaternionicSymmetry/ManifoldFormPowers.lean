import QuaternionicSymmetry.ManifoldDeRhamDegreeZero
import QuaternionicSymmetry.ExteriorContinuousPowers

/-! Smooth repeated wedge products of genuine manifold forms. -/
namespace QuaternionicSymmetry.ManifoldFormPowers

open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldDeRhamDegreeZero
  ExteriorContinuousPowers ContinuousWedgeUnit
open scoped Manifold ContDiff Topology

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {d : ℕ}

noncomputable def formPower (α : Form 𝓘(ℝ, E) M d) :
    (n : ℕ) → Form 𝓘(ℝ, E) M (d*n)
  | 0 => oneForm
  | n+1 => castForm (Nat.mul_succ d n).symm (formWedge (formPower α n) α)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem inChartModel_formPower (α : Form 𝓘(ℝ, E) M d) (n : ℕ) (x : M) (y : E) :
    inChartModel x (formPower α n) y = wedgePower (inChartModel x α y) n := by
  induction n with
  | zero => simp only [formPower, inChartModel_oneForm, wedgePower]
  | succ n ih =>
    simp only [formPower, inChartModel_castForm, inChartModel_formWedge, ih, wedgePower]
    rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formPower_smooth (α : Form 𝓘(ℝ, E) M d) (hα : ChartSmooth α) (n : ℕ) :
    ChartSmooth (formPower α n) := by
  induction n with
  | zero => exact oneForm_smooth
  | succ n ih =>
    exact chartSmooth_castForm _ _ (chartSmooth_formWedge _ _ ih hα)

theorem formPower_closed (α : Form 𝓘(ℝ, E) M d) (hα : ChartSmooth α)
    (hcα : exteriorDerivative α = 0) (n : ℕ) :
    exteriorDerivative (formPower α n) = 0 := by
  induction n with
  | zero => exact oneForm_closed
  | succ n ih =>
    unfold formPower
    rw [exteriorDerivative_castForm,
      formWedge_closed _ _ (formPower_smooth α hα n) hα ih hcα]
    cases Nat.mul_succ d n
    rfl

end QuaternionicSymmetry.ManifoldFormPowers
