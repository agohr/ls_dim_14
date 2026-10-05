import QuaternionicSymmetry.ManifoldQuaternionicSchurLocalConstancy
import Mathlib.Analysis.Calculus.MeanValue

/-! On each valid chart target, the actual Einstein factor has locally
constant fibers by Schur's lemma. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicEinsteinFactorLocallyConstant
open ManifoldQuaternionicConnection
open ManifoldQuaternionicEinsteinFactor
open ManifoldQuaternionicSchurLocalConstancy
open ManifoldQuaternionicKSWEq38Input
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem target_factor_fiber_open
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (c : E) (hc : c ≠ 0)
    (hcard : 3 ≤ Module.finrank ℝ E) (r : ℝ) :
    IsOpen ((extChartAt 𝓘(ℝ,E) p).target ∩
      (einsteinFactor Q D p c) ⁻¹' {r}) := by
  let U := (extChartAt 𝓘(ℝ,E) p).target
  have hdiff : DifferentiableOn ℝ (einsteinFactor Q D p c) U := by
    intro y hy
    exact (einsteinFactor_differentiableAt Q D p y hy c hc).differentiableWithinAt
  have hzero : U.EqOn (fderiv ℝ (einsteinFactor Q D p c)) 0 := by
    intro y hy
    exact einsteinFactor_fderiv_eq_zero Q D S hdecomp p c hc y hy hcard
  exact (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).isOpen_inter_preimage_of_fderiv_eq_zero
    hdiff hzero {r}

end
end QuaternionicSymmetry.ManifoldQuaternionicEinsteinFactorLocallyConstant
