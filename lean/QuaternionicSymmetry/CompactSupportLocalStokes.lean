import QuaternionicSymmetry.ContinuousTopFormCoefficient
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Local Stokes for compactly supported smooth forms on a real vector space.
The measure here is an actual additive Haar measure. -/
namespace QuaternionicSymmetry.CompactSupportLocalStokes

open MeasureTheory Measure
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] in
theorem integrable_directionalDerivative {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (v : E) :
    Integrable (fun x => fderiv ℝ g x v) μ := by
  exact ((hg.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v)

theorem integral_directionalDerivative_eq_zero {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (v : E) :
    (∫ x, fderiv ℝ g x v ∂μ) = 0 := by
  have hd := integrable_directionalDerivative (μ := μ) hg hc v
  have hi := hg.continuous.integrable_of_hasCompactSupport (μ := μ) hc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := fun _ : E => (1 : ℝ)) (g := g) (v := v)
    (by simp) (by simpa using hd)
    (by simpa using hi) (differentiable_const _) (hg.differentiable (by simp))
  simpa using h

theorem integral_extDeriv_eq_zero {n : ℕ}
    {α : E → E [⋀^Fin n]→L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hc : HasCompactSupport α)
    (v : Fin (n + 1) → E) : (∫ x, extDeriv α x v ∂μ) = 0 := by
  classical
  have hs (i : Fin (n + 1)) : ContDiff ℝ ∞ (fun x => α x (i.removeNth v)) :=
    (ContinuousTopFormCoefficient.evaluation (i.removeNth v)).contDiff.comp hα
  have hcs (i : Fin (n + 1)) : HasCompactSupport (fun x => α x (i.removeNth v)) :=
    hc.comp_left (g := fun β : E [⋀^Fin n]→L[ℝ] ℝ => β (i.removeNth v)) rfl
  simp_rw [extDeriv_apply (hα.differentiable (by simp) _)]
  simp only [zsmul_eq_mul]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul, integral_directionalDerivative_eq_zero (hs _) (hcs _)]
    simp
  · intro i _
    exact (integrable_directionalDerivative (hs i) (hcs i) (v i)).const_mul _

end QuaternionicSymmetry.CompactSupportLocalStokes
