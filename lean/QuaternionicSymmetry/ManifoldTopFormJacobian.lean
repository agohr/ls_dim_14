import QuaternionicSymmetry.ManifoldQuaternionicVolume
import QuaternionicSymmetry.ContinuousTopFormCoefficient

/-! Exact determinant and absolute-Jacobian transformation laws for genuine
manifold top forms, supplying the local volume-measure gluing identity. -/
namespace QuaternionicSymmetry.ManifoldTopFormJacobian

open Module ManifoldDifferentialForms ContinuousTopFormCoefficient
open scoped Manifold ContDiff Topology
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
noncomputable section

def signedChartDensity (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (p : M) (y : E) : ℝ :=
  inChartModel p ν y (Module.finBasis ℝ E)

def chartDensity (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (p : M) (y : E) : ℝ :=
  |signedChartDensity ν p y|

theorem signedChartDensity_transition (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (p q : M) {y : E} (hp : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hq : (extChartAt 𝓘(ℝ, E) p).symm y ∈ (extChartAt 𝓘(ℝ, E) q).source) :
    signedChartDensity ν p y =
      (fderiv ℝ ((extChartAt 𝓘(ℝ, E) q) ∘ (extChartAt 𝓘(ℝ, E) p).symm) y).toLinearMap.det *
        signedChartDensity ν q
          ((extChartAt 𝓘(ℝ, E) q) ((extChartAt 𝓘(ℝ, E) p).symm y)) := by
  unfold signedChartDensity
  rw [inChartModel_change ν p q y hp hq]
  exact eval_comp_basis _ _ _

theorem chartDensity_transition (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (p q : M) {y : E} (hp : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hq : (extChartAt 𝓘(ℝ, E) p).symm y ∈ (extChartAt 𝓘(ℝ, E) q).source) :
    chartDensity ν p y =
      |(fderiv ℝ ((extChartAt 𝓘(ℝ, E) q) ∘ (extChartAt 𝓘(ℝ, E) p).symm) y).toLinearMap.det| *
        chartDensity ν q
          ((extChartAt 𝓘(ℝ, E) q) ((extChartAt 𝓘(ℝ, E) p).symm y)) := by
  simp only [chartDensity, signedChartDensity_transition ν p q hp hq, abs_mul]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem chartDensity_continuousOn (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hν : ChartSmooth ν) (p : M) :
    ContinuousOn (chartDensity ν p) (extChartAt 𝓘(ℝ, E) p).target := by
  exact ((hν p).continuousLinearMap_comp (evaluation (Module.finBasis ℝ E))).continuousOn.abs

end
end QuaternionicSymmetry.ManifoldTopFormJacobian
