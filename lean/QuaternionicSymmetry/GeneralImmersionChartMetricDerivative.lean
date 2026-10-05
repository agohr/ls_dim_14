import QuaternionicSymmetry.GeneralImmersionChartMetricJet
import QuaternionicSymmetry.GeneralImmersionChartPullbackMetric

/-! The first metric jet of a genuine immersion-pullback metric is the
ambient second fundamental derivative pairing, in arbitrary charts. -/

namespace QuaternionicSymmetry.GeneralImmersionChartMetricDerivative

open Manifold Bundle GeneralLeviCivitaSource
open GeneralImmersionChartPullbackMetric GeneralImmersionChartMetricJet
open scoped Manifold ContDiff Topology
noncomputable section

variable {E V M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartMetric_fderiv_eq_ambient_hessian
    (f : M → V) (g : V →L[ℝ] V →L[ℝ] ℝ)
    (metric : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f)
    (hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,E) x),
      metric.inner x v w = g (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x w))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v w : E) :
    let F := f ∘ (extChartAt 𝓘(ℝ,E) p).symm
    let dF := fderiv ℝ F
    let H := fderiv ℝ dF y
    fderiv ℝ (fun z => chartMetric metric p z v w) y u =
      g (H u v) (dF y w) + g (dF y v) (H u w) := by
  let F := f ∘ (extChartAt 𝓘(ℝ,E) p).symm
  let dF := fderiv ℝ F
  let H := fderiv ℝ dF y
  have hσ : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hF : ContDiffAt ℝ 2 F y := by
    exact ((hf.contMDiffAt.comp y hσ).contDiffAt).of_le (by decide)
  have heq : (fun z => chartMetric metric p z v w) =ᶠ[𝓝 y]
      (fun z => g (dF z v) (dF z w)) := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
    exact chartMetric_eq_ambient_chart_derivatives f g metric hf hmetric p z hz v w
  rw [heq.fderiv_eq]
  exact fderiv_ambient_pullback_pairing F g y u v w hF

end
end QuaternionicSymmetry.GeneralImmersionChartMetricDerivative
