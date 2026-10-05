import QuaternionicSymmetry.ManifoldQuaternionicChartStokes
import QuaternionicSymmetry.ManifoldQuaternionicDensityIntegration
import QuaternionicSymmetry.ManifoldFiniteFormPartition

/-! Global Stokes from the verified local volume-measure restrictions.
The measure premise is intended to be discharged by canonical chart gluing. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicGlobalStokes

open MeasureTheory Measure Set ManifoldDifferentialForms ManifoldDeRhamWedge
  ManifoldFormLocalization ManifoldQuaternionicMetric ManifoldQuaternionicVolume
  ManifoldQuaternionicVolumeCoefficient ManifoldQuaternionicDensityIntegration
  ManifoldQuaternionicChartStokes ManifoldTopFormLocalMeasure ManifoldFiniteFormPartition
open scoped Manifold ContDiff Topology
set_option maxHeartbeats 800000
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (μ : Measure M)
  (hlocal : ∀ p : M, μ.restrict (extChartAt 𝓘(ℝ, E) p).source =
    chartMeasure (fundamentalTopForm Q) p)

include hlocal in
theorem integral_localized_exact {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E)
    (p : M) (f : M → ℝ) (α : Form 𝓘(ℝ, E) M n) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ (extChartAt 𝓘(ℝ, E) p).source)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hα : ChartSmooth α) :
    (∫ x, scalarDensity Q (castForm hdim (exteriorDerivative (scalarMultiply f α))) x ∂μ) =
      0 := by
  have hz : ∀ x, x ∉ (extChartAt 𝓘(ℝ, E) p).source →
      scalarDensity Q (castForm hdim (exteriorDerivative (scalarMultiply f α))) x = 0 := by
    intro x hx
    by_contra h
    exact hx (hsub (support_localized_exact_density_subset Q hdim f α h))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  change (∫ x, _ ∂μ.restrict (extChartAt 𝓘(ℝ, E) p).source) = 0
  rw [hlocal p]
  exact chartMeasure_integral_localized_exact Q hdim p f α hc hsub hf hα

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
private theorem castForm_finset_sum {k l : ℕ} (h : k = l) {ι : Type*}
    (s : Finset ι) (β : ι → Form 𝓘(ℝ, E) M k) :
    castForm h (∑ i ∈ s, β i) = ∑ i ∈ s, castForm h (β i) := by
  cases h
  rfl

variable [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]

include hlocal in
theorem integral_exact_eq_zero {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E)
    (α : Form 𝓘(ℝ, E) M n) (hα : ChartSmooth α) :
    (∫ x, scalarDensity Q (castForm hdim (exteriorDerivative α)) x ∂μ) = 0 := by
  classical
  obtain ⟨s, ρ, hρ⟩ := exists_finite_chart_partition (E := E) (M := M)
  let β (i : s) : SmoothTopForms (E := E) (M := M) :=
    ⟨castForm hdim (exteriorDerivative (scalarMultiply (ρ i) α)),
      chartSmooth_castForm _ _ (chartSmooth_exteriorDerivative _
        (partition_summand_smooth ρ α hα i))⟩
  let γ : SmoothTopForms (E := E) (M := M) :=
    ⟨castForm hdim (exteriorDerivative α),
      chartSmooth_castForm _ _ (chartSmooth_exteriorDerivative _ hα)⟩
  have hs : ∑ i, β i = γ := by
    apply Subtype.ext
    change (∑ i, β i).val = γ.val
    simp only [Submodule.coe_sum, β, γ]
    rw [← castForm_finset_sum, partition_sum_exteriorDerivative ρ α hα]
  have hz (i : s) : densityIntegral Q μ (β i) = 0 := by
    apply integral_localized_exact Q μ hlocal hdim (i : M) (ρ i) α
    · exact HasCompactSupport.of_compactSpace _
    · simpa only [extChartAt_source] using hρ i
    · exact (ρ i).contMDiff
    · exact hα
  have h := congrArg (densityIntegral Q μ) hs
  rw [_root_.map_sum] at h
  simpa only [hz, Finset.sum_const_zero] using h.symm

end QuaternionicSymmetry.ManifoldQuaternionicGlobalStokes
