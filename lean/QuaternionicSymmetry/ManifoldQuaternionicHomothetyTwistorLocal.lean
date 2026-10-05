import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorHomeomorph
import QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
import QuaternionicSymmetry.ManifoldTwistorLocalContactProjectorOverlap

/-! Homothety leaves the local twistor horizontal connection and complex
operator unchanged in raw chart and sphere coordinates. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorLocal
open ManifoldQuaternionicHomothetyReduction ManifoldQuaternionicHomothetyConnection
open ManifoldTwistorLocalAlmostComplex ManifoldTwistorHorizontalConnection
open ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem inducedForm_rescale (s : ℝ) (hs : s ≠ 0) (p : M) :
    ManifoldQuaternionicAdjointConnection.inducedForm
      (rescaleMetric Q s hs) (rescaleConnection Q D s hs) p =
      ManifoldQuaternionicAdjointConnection.inducedForm Q D p := rfl

omit [FiniteDimensional ℝ E] in
theorem chartBaseComplex_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (a : ManifoldTwistorSphereBundle.coefficientSphere) :
    chartBaseComplex (rescaleMetric Q s hs) p y a = chartBaseComplex Q p y a := by
  ext v
  change (s⁻¹ • Q.frames.fromFrame (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y))
      (baseComplex (Q.reduction.Q (achart E p)) a
        ((s • Q.frames.toFrame (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y)) v)) = _
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [mul_inv_cancel₀ hs, one_smul]
  rfl

theorem connectionVertical_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : ManifoldTwistorSphereBundle.coefficientSphere) :
    connectionVertical (rescaleMetric Q s hs) (rescaleConnection Q D s hs)
      p y hy a = connectionVertical Q D p y hy a := by
  ext u t
  rfl

theorem connectionSplit_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : ManifoldTwistorSphereBundle.coefficientSphere) :
    connectionSplit (rescaleMetric Q s hs) (rescaleConnection Q D s hs)
      p y hy a = connectionSplit Q D p y hy a := by
  apply LinearEquiv.ext
  intro uv
  change (uv.1, uv.2 + connectionVertical (rescaleMetric Q s hs)
    (rescaleConnection Q D s hs) p y hy a uv.1) =
    (uv.1, uv.2 + connectionVertical Q D p y hy a uv.1)
  rw [connectionVertical_rescale]

omit [FiniteDimensional ℝ E] in
theorem chartSplitComplex_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (a : ManifoldTwistorSphereBundle.coefficientSphere) :
    chartSplitComplex (rescaleMetric Q s hs) p y a = chartSplitComplex Q p y a := by
  apply LinearMap.ext
  intro uv
  change (chartBaseComplex (rescaleMetric Q s hs) p y a uv.1,
    ManifoldTwistorVerticalComplex.verticalComplex a uv.2) =
    (chartBaseComplex Q p y a uv.1,
      ManifoldTwistorVerticalComplex.verticalComplex a uv.2)
  rw [chartBaseComplex_rescale]

theorem localTwistorComplex_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : ManifoldTwistorSphereBundle.coefficientSphere) :
    localTwistorComplex (rescaleMetric Q s hs) (rescaleConnection Q D s hs)
      p y hy a = localTwistorComplex Q D p y hy a := by
  simp only [localTwistorComplex, connectionSplit_rescale, chartSplitComplex_rescale]

theorem localHorizontalPlaneProjection_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : ManifoldTwistorSphereBundle.coefficientSphere) :
    localHorizontalPlaneProjection (rescaleMetric Q s hs) (rescaleConnection Q D s hs)
      p y hy a = localHorizontalPlaneProjection Q D p y hy a := by
  apply LinearMap.ext
  intro uv
  change (uv.1, -connectionVertical (rescaleMetric Q s hs)
    (rescaleConnection Q D s hs) p y hy a uv.1) =
    (uv.1, -connectionVertical Q D p y hy a uv.1)
  rw [connectionVertical_rescale]

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorLocal
