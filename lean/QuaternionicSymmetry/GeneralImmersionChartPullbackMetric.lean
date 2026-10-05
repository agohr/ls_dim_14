import QuaternionicSymmetry.ManifoldImmersionPullbackMetricGeneral
import QuaternionicSymmetry.GeneralLeviCivitaSource

/-! The genuine chart metric of a derivative-pullback immersion metric
is the fixed ambient pairing of the chartwise immersion derivatives. -/

namespace QuaternionicSymmetry.GeneralImmersionChartPullbackMetric

open Manifold Bundle GeneralLeviCivitaSource
open scoped Manifold ContDiff Topology
noncomputable section

variable {E V M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (f : M → V) (g : V →L[ℝ] V →L[ℝ] ℝ)
  (metric : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
    (TangentSpace 𝓘(ℝ,E) : M → Type _))

theorem chartMetric_eq_ambient_chart_derivatives
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f)
    (hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,E) x),
      metric.inner x v w = g (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x w))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v : E) :
    chartMetric metric p y u v =
      g (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ,E) p).symm) y u)
        (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ,E) p).symm) y v) := by
  let φ := (extChartAt 𝓘(ℝ,E) p).symm
  have hφ : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) φ y :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)).mdifferentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp y
    (hf.mdifferentiableAt (by simp)) hφ
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) (f ∘ φ) y = _ at hcomp
  rw [mfderiv_eq_fderiv] at hcomp
  change metric.inner (φ y)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) φ y u)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) φ y v) = _
  rw [hmetric]
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply]
  rw [← hcomp]
  rfl

end
end QuaternionicSymmetry.GeneralImmersionChartPullbackMetric
