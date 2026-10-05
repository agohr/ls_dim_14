import QuaternionicSymmetry.ManifoldQuaternionicLocalSynthMetric

/-! Smoothness of a fixed-chart quaternionic endomorphism for a fixed
coefficient vector. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicLocalSynthSmooth
open ManifoldQuaternionicMetric
open ManifoldQuaternionicLocalGaugeTransport
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem smooth_localTangentSynth (i : atlas E M) (a : Fin 3 → ℝ) :
    ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun x => localTangentSynth Q i x a)
      (Q.frames.adaptedCore.baseSet i) := by
  have hconst : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun _ : M => synth (Q.reduction.Q i) a)
      (Q.frames.adaptedCore.baseSet i) := contMDiffOn_const
  exact (Q.frames.smooth_from i).clm_comp
    (hconst.clm_comp (Q.frames.smooth_to i))

end
end QuaternionicSymmetry.ManifoldQuaternionicLocalSynthSmooth
