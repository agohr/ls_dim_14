import QuaternionicSymmetry.ManifoldChartStokes
import QuaternionicSymmetry.ManifoldQuaternionicVolumeCoefficient
import QuaternionicSymmetry.ManifoldTopFormJacobian
import QuaternionicSymmetry.ManifoldTopFormChartIntegration
import QuaternionicSymmetry.ManifoldFormSupport

/-! The quaternionic scalar-density integral of a localized exact top form
vanishes in its chart, with the actual absolute volume density. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicChartStokes

open MeasureTheory Measure Set ManifoldDifferentialForms ManifoldDeRhamWedge
  ManifoldFormLocalization ManifoldQuaternionicMetric ManifoldQuaternionicVolume
  ManifoldQuaternionicVolumeCoefficient ManifoldTopFormJacobian
open scoped Manifold ContDiff Topology
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  {μ : Measure E} [IsAddHaarMeasure μ]

theorem integral_localized_exact_density {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E)
    (p : M) (f : M → ℝ) (α : Form 𝓘(ℝ, E) M n) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ (extChartAt 𝓘(ℝ, E) p).source)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hα : ChartSmooth α) :
    (∫ y in (extChartAt 𝓘(ℝ, E) p).target,
      scalarDensity Q (castForm hdim (exteriorDerivative (scalarMultiply f α)))
        ((extChartAt 𝓘(ℝ, E) p).symm y) *
      chartDensity (fundamentalTopForm Q) p y ∂μ) = 0 := by
  let g : E → ℝ := signedChartDensity (fundamentalTopForm Q) p
  have hg : ContinuousOn g (extChartAt 𝓘(ℝ, E) p).target :=
    ((fundamentalTopForm_smooth Q p).continuousLinearMap_comp
      (ContinuousTopFormCoefficient.evaluation (Module.finBasis ℝ E))).continuousOn
  have hne (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) : g y ≠ 0 :=
    ContinuousTopFormCoefficient.eval_basis_ne_zero (Module.finBasis ℝ E) _
      (fundamentalTopForm_chart_ne_zero Q p hy)
  have hzero := ManifoldChartStokes.integral_signed_localized_exteriorDerivative
    (μ := μ) p f α hc hsub hf hα g hg hne ((Module.finBasis ℝ E) ∘ finCongr hdim)
  apply Eq.trans _ hzero
  apply setIntegral_congr_fun (isOpen_extChartAt_target p).measurableSet
  intro y hy
  dsimp only
  rw [scalarDensity_chart Q _ p hy, inChartModel_castForm, castAlternating_apply]
  change _ / g y * |g y| = (|g y| / g y) * _
  ring

variable [MeasurableSpace M] [BorelSpace M]

omit [IsAddHaarMeasure μ] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] in
theorem support_scalarDensity_subset
    (α : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) :
    Function.support (scalarDensity Q α) ⊆ ManifoldFormSupport.support α := by
  intro x hx ha
  apply hx
  change ContinuousTopFormCoefficient.coefficient (tangentBasis x)
    (fundamentalTopForm Q x) (α x) = 0
  rw [ha, map_zero]

omit [IsAddHaarMeasure μ] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] in
theorem support_localized_exact_density_subset {n : ℕ}
    (hdim : n + 1 = Module.finrank ℝ E) (f : M → ℝ) (α : Form 𝓘(ℝ, E) M n) :
    Function.support (scalarDensity Q (castForm hdim
      (exteriorDerivative (scalarMultiply f α)))) ⊆ tsupport f :=
  (support_scalarDensity_subset Q _).trans
    ((ManifoldFormSupport.support_castForm_subset hdim _).trans
      ((ManifoldFormSupport.support_derivative_subset _).trans
        (ManifoldFormSupport.tsupport_scalarMultiply_subset f α)))

omit [IsAddHaarMeasure μ] in
theorem chartMeasure_integral_localized_exact {n : ℕ}
    (hdim : n + 1 = Module.finrank ℝ E)
    (p : M) (f : M → ℝ) (α : Form 𝓘(ℝ, E) M n) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ (extChartAt 𝓘(ℝ, E) p).source)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hα : ChartSmooth α) :
    (∫ x, scalarDensity Q (castForm hdim (exteriorDerivative (scalarMultiply f α))) x
      ∂ManifoldTopFormLocalMeasure.chartMeasure (fundamentalTopForm Q) p) = 0 := by
  rw [ManifoldTopFormChartIntegration.integral_chartMeasure _ (fundamentalTopForm_smooth Q)
    p _ ((scalarDensity_smooth Q _ (chartSmooth_castForm _ _
      (chartSmooth_exteriorDerivative _ (scalarMultiply_smooth f α hf hα)))).continuous)]
  exact integral_localized_exact_density Q hdim p f α hc hsub hf hα

end QuaternionicSymmetry.ManifoldQuaternionicChartStokes
