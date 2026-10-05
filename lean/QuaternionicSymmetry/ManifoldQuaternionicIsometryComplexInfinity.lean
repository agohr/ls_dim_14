import QuaternionicSymmetry.ManifoldQuaternionicIsometryComplexAtlas
import QuaternionicSymmetry.ComplexSmoothRealInfinity

/-! The derivative-induced lift of a genuine quaternionic isometry is
complex-C∞ in the compatible twistor atlas. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryComplexInfinity

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryComplexAtlas
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ComplexSmoothRealInfinity
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- The actual twistor lift is complex-C∞, not merely pointwise holomorphic,
in every compatible twistor atlas. -/
theorem sphereTotalMap_contMDiff_complex_infty
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (f : QuaternionicIsometries Q) :
    letI := B.charts
    ContMDiff 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel n) ∞ (sphereTotalMap Q f) := by
  letI := B.charts
  letI := B.realManifold
  letI := B.complexManifold
  let F := ComplexTwistorModel n
  have hReal : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (sphereTotalMap Q f) :=
    sphereTotalMap_realSmooth_in_compatibleAtlas Q D B f
  have hComplex : MDifferentiable 𝓘(ℂ,F) 𝓘(ℂ,F) (sphereTotalMap Q f) :=
    sphereTotalMap_mdifferentiable_complex Q D B f
  obtain ⟨hcont, hRealCharts⟩ := contMDiff_iff.mp hReal
  obtain ⟨_, hComplexCharts⟩ := mdifferentiable_iff.mp hComplex
  apply contMDiff_iff.mpr
  refine ⟨hcont, ?_⟩
  intro x y
  let s : Set F := (extChartAt 𝓘(ℂ,F) x).target ∩
    (extChartAt 𝓘(ℂ,F) x).symm ⁻¹'
      ((sphereTotalMap Q f) ⁻¹' (extChartAt 𝓘(ℂ,F) y).source)
  have hs : IsOpen s := by
    apply (continuousOn_extChartAt_symm (I := 𝓘(ℂ,F)) x).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓘(ℂ,F)) x)
    exact (isOpen_extChartAt_source (I := 𝓘(ℂ,F)) y).preimage hcont
  have hR : ContDiffOn ℝ ∞
      (extChartAt 𝓘(ℂ,F) y ∘ sphereTotalMap Q f ∘
        (extChartAt 𝓘(ℂ,F) x).symm) s := by
    simpa only [s] using hRealCharts x y
  have hC : DifferentiableOn ℂ
      (extChartAt 𝓘(ℂ,F) y ∘ sphereTotalMap Q f ∘
        (extChartAt 𝓘(ℂ,F) x).symm) s := by
    simpa only [s] using hComplexCharts x y
  exact contDiffOn_infty_of_real_complex hs hR hC

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryComplexInfinity
