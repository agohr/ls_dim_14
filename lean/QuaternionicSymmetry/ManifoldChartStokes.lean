import QuaternionicSymmetry.ManifoldChartLocalization
import QuaternionicSymmetry.SignedLocalStokes

/-! Stokes for actual tangent forms localized inside one chart. The cutoff's
compact support and subordination imply smooth compact zero extension. -/
namespace QuaternionicSymmetry.ManifoldChartStokes

open Set Filter MeasureTheory Measure ManifoldDifferentialForms
  ManifoldFormLocalization ManifoldChartLocalization
open scoped Manifold ContDiff Topology
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {μ : Measure E} [IsAddHaarMeasure μ] {n : ℕ}

theorem integral_localized_exteriorDerivative (p : M) (f : M → ℝ)
    (α : Form 𝓘(ℝ, E) M n) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ (extChartAt 𝓘(ℝ, E) p).source)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hα : ChartSmooth α)
    (v : Fin (n + 1) → E) :
    (∫ y in (extChartAt 𝓘(ℝ, E) p).target,
      inChartModel p (exteriorDerivative (scalarMultiply f α)) y v ∂μ) = 0 := by
  have hsm := scalarMultiply_smooth f α hf hα
  have hloc := localizedChartForm_smooth p f α hc hsub hf hα
  have heq (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
      inChartModel p (exteriorDerivative (scalarMultiply f α)) y v =
        extDeriv (localizedChartForm p f α) y v := by
    rw [inChartModel_exteriorDerivative _ hsm p hy]
    have hev : localizedChartForm p f α =ᶠ[𝓝 y] inChartModel p (scalarMultiply f α) := by
      filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
      exact localizedChartForm_eq p f α hz
    rw [hev.extDeriv_eq]
  calc
    _ = ∫ y in (extChartAt 𝓘(ℝ, E) p).target,
        extDeriv (localizedChartForm p f α) y v ∂μ :=
      setIntegral_congr_fun (isOpen_extChartAt_target p).measurableSet heq
    _ = 0 := CompactSupportDomainStokes.setIntegral_extDeriv_eq_zero
      (isOpen_extChartAt_target p) hloc.contDiffOn
      (localizedChartForm_compactSupport p f α hc hsub)
      (tsupport_localizedChartForm_subset p f α hc hsub) v

theorem integral_signed_localized_exteriorDerivative (p : M) (f : M → ℝ)
    (α : Form 𝓘(ℝ, E) M n) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ (extChartAt 𝓘(ℝ, E) p).source)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hα : ChartSmooth α)
    (g : E → ℝ) (hg : ContinuousOn g (extChartAt 𝓘(ℝ, E) p).target)
    (hne : ∀ y ∈ (extChartAt 𝓘(ℝ, E) p).target, g y ≠ 0)
    (v : Fin (n + 1) → E) :
    (∫ y in (extChartAt 𝓘(ℝ, E) p).target,
      SignedLocalStokes.orientationSign (g y) *
        inChartModel p (exteriorDerivative (scalarMultiply f α)) y v ∂μ) = 0 := by
  have hsm := scalarMultiply_smooth f α hf hα
  have hloc := localizedChartForm_smooth p f α hc hsub hf hα
  have hzero := SignedLocalStokes.setIntegral_signed_extDeriv_eq_zero
    (μ := μ) (isOpen_extChartAt_target p) hg hne hloc.contDiffOn
    (localizedChartForm_compactSupport p f α hc hsub)
    (tsupport_localizedChartForm_subset p f α hc hsub) v
  apply Eq.trans _ hzero
  apply setIntegral_congr_fun (isOpen_extChartAt_target p).measurableSet
  intro y hy
  dsimp only
  congr 1
  rw [inChartModel_exteriorDerivative _ hsm p hy]
  have hev : localizedChartForm p f α =ᶠ[𝓝 y] inChartModel p (scalarMultiply f α) := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
    exact localizedChartForm_eq p f α hz
  rw [hev.extDeriv_eq]

end QuaternionicSymmetry.ManifoldChartStokes
