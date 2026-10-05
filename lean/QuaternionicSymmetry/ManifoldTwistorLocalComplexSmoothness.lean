import QuaternionicSymmetry.ManifoldTwistorPreferredChartDerivative
/-! Smoothness of the adapted-frame-conjugated horizontal quaternionic
operator in raw manifold chart coordinates, with the coefficient vector
allowed to vary in ambient three-space. -/
namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open QuaternionicSymmetry.VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem frameTo_chart_smooth (p : M) :
    ContDiffOn ℝ ∞ (fun y : E => Q.frames.toFrame (achart E p)
      ((extChartAt 𝓘(ℝ,E) p).symm y)) (extChartAt 𝓘(ℝ,E) p).target := by
  have hmaps : Set.MapsTo (extChartAt 𝓘(ℝ,E) p).symm
      (extChartAt 𝓘(ℝ,E) p).target
      (Q.frames.adaptedCore.baseSet (achart E p)) := by
    intro y hy
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) p).map_target hy
  have h := (Q.frames.smooth_to (achart E p)).comp
    (contMDiffOn_extChartAt_symm p) hmaps
  exact h.contDiffOn
omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem frameFrom_chart_smooth (p : M) :
    ContDiffOn ℝ ∞ (fun y : E => Q.frames.fromFrame (achart E p)
      ((extChartAt 𝓘(ℝ,E) p).symm y)) (extChartAt 𝓘(ℝ,E) p).target := by
  have hmaps : Set.MapsTo (extChartAt 𝓘(ℝ,E) p).symm
      (extChartAt 𝓘(ℝ,E) p).target
      (Q.frames.adaptedCore.baseSet (achart E p)) := by
    intro y hy
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) p).map_target hy
  have h := (Q.frames.smooth_from (achart E p)).comp
    (contMDiffOn_extChartAt_symm p) hmaps
  exact h.contDiffOn

private abbrev V := Fin 3 → ℝ

def ambientBaseComplex (p : M) (y : E) (a : V) : E →L[ℝ] E :=
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  (Q.frames.fromFrame (achart E p) x).comp
    ((synth (Q.reduction.Q (achart E p)) a).comp
      (Q.frames.toFrame (achart E p) x))

omit [FiniteDimensional ℝ E] in
theorem ambientBaseComplex_smooth (p : M) :
    ContDiffOn ℝ ∞
      (fun ya : E × V => ambientBaseComplex Q p ya.1 ya.2)
      ((extChartAt 𝓘(ℝ,E) p).target ×ˢ Set.univ) := by
  have hfrom : ContDiffOn ℝ ∞
      (fun ya : E × V => Q.frames.fromFrame (achart E p)
        ((extChartAt 𝓘(ℝ,E) p).symm ya.1))
      ((extChartAt 𝓘(ℝ,E) p).target ×ˢ Set.univ) :=
    (frameFrom_chart_smooth Q p).comp contDiffOn_fst (by
      intro x hx
      exact hx.1)
  have hto : ContDiffOn ℝ ∞
      (fun ya : E × V => Q.frames.toFrame (achart E p)
        ((extChartAt 𝓘(ℝ,E) p).symm ya.1))
      ((extChartAt 𝓘(ℝ,E) p).target ×ˢ Set.univ) :=
    (frameTo_chart_smooth Q p).comp contDiffOn_fst (by
      intro x hx
      exact hx.1)
  have hsynth : ContDiffOn ℝ ∞
      (fun ya : E × V => synth (Q.reduction.Q (achart E p)) ya.2)
      ((extChartAt 𝓘(ℝ,E) p).target ×ˢ Set.univ) :=
    ((synth (Q.reduction.Q (achart E p))).contDiff.contDiffOn
      (s := Set.univ)).comp contDiffOn_snd (by
      intro x hx
      exact Set.mem_univ _)
  simpa only [ambientBaseComplex] using hfrom.clm_comp (hsynth.clm_comp hto)
end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
