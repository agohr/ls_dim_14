import QuaternionicSymmetry.ManifoldQuaternionicEinsteinFactorLocallyConstant

/-! The chart Einstein factor is an intrinsic scalar, expressed through the
actual preferred scalar-curvature contraction. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicPreferredEinsteinFactor
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicEinsteinFactor
open ManifoldQuaternionicKSWScalarInput
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

def preferredEinsteinFactor (c : E) (x : M) : ℝ :=
  einsteinFactor Q D x c (extChartAt 𝓘(ℝ,E) x x)

theorem factor_chart_eq_preferred
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    einsteinFactor Q D p c y =
      preferredEinsteinFactor Q D c ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hx := (extChartAt 𝓘(ℝ,E) p).map_target hy
  have hxy := (extChartAt 𝓘(ℝ,E) p).right_inv hy
  have hlocal := localScalarCurvature_eq_preferred Q D p x hx
    (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)
  have hlocal' : localScalarCurvature Q D p y hy =
      preferredScalarCurvature Q D x := by
    simpa only [x, hxy] using hlocal
  rw [einsteinFactor_eq_scalarRatio Q D S hdecomp p y hy c hc]
  rw [preferredEinsteinFactor,
    einsteinFactor_eq_scalarRatio Q D S hdecomp x
      (extChartAt 𝓘(ℝ,E) x x)
      ((extChartAt 𝓘(ℝ,E) x).map_source (by simp)) c hc]
  simp only [scalarRatio, hlocal', preferredScalarCurvature]

end
end QuaternionicSymmetry.ManifoldQuaternionicPreferredEinsteinFactor
