import QuaternionicSymmetry.ManifoldQuaternionicJointSphereContinuity

/-! The two-fixed-chart spatial derivative is smoothly parameterized by the
full BG-R3 isometry Lie group, before restriction to quaternionic isometries. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullMovingAdaptedSmooth

open Manifold
open ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- A full metric isometry need not preserve quaternionic structure, but
its actual spatial derivative can still be expressed in the fixed adapted
frames at `x₀` and `g₀ x₀`. -/
def fullMovingAdaptedDerivative
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (g₀ : letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M)
    (x₀ : M)
    (p : (letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M) × M) :
    E →L[ℝ] E := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  exact (Q.frames.toFrame (achart E (g₀ x₀)) (p.1 p.2)).comp
    (((inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
      (fun q : (M ≃ᵢ M) × M => q.1 q.2)
      (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
        (fun q : (M ≃ᵢ M) × M => q.1 q.2))
      (g₀,x₀) p).comp (ContinuousLinearMap.inr ℝ V E)).comp
      (Q.frames.fromFrame (achart E x₀) p.2))

theorem contMDiffAt_fullMovingAdaptedDerivative
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (g₀ : letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M)
    (x₀ : M) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContMDiffAt (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fullMovingAdaptedDerivative Q hChart hManifold g₀ x₀) (g₀,x₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  let a : (M ≃ᵢ M) × M → M := fun p => p.1 p.2
  have hD : ContMDiffAt (𝓘(ℝ,V).prod 𝓘(ℝ,E))
      𝓘(ℝ,(V × E →L[ℝ] E)) ∞
      (inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id a
        (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) a) (g₀,x₀)) (g₀,x₀) :=
    (hAction.contMDiffAt (x := (g₀,x₀))).mfderiv_const (by simp)
  have hpartial : ContMDiffAt (𝓘(ℝ,V).prod 𝓘(ℝ,E))
      𝓘(ℝ,E →L[ℝ] E) ∞
      (fun p => (inTangentCoordinates
        (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id a
        (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) a)
        (g₀,x₀) p).comp (ContinuousLinearMap.inr ℝ V E)) (g₀,x₀) :=
    (hD.clm_comp contMDiffAt_const)
  have hto : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (Q.frames.toFrame (achart E (g₀ x₀))) (g₀ x₀) :=
    (Q.frames.smooth_to _).contMDiffAt
      ((Q.frames.adaptedCore.isOpen_baseSet _).mem_nhds
        (Q.frames.adaptedCore.mem_baseSet_at _))
  have hfrom : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (Q.frames.fromFrame (achart E x₀)) x₀ :=
    (Q.frames.smooth_from _).contMDiffAt
      ((Q.frames.adaptedCore.isOpen_baseSet _).mem_nhds
        (Q.frames.adaptedCore.mem_baseSet_at _))
  have hto' : ContMDiffAt (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun p : (M ≃ᵢ M) × M => Q.frames.toFrame (achart E (g₀ x₀)) (p.1 p.2))
      (g₀,x₀) := hto.comp (g₀,x₀) (hAction.contMDiffAt (x := (g₀,x₀)))
  have hfrom' : ContMDiffAt (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun p : (M ≃ᵢ M) × M => Q.frames.fromFrame (achart E x₀) p.2)
      (g₀,x₀) := hfrom.comp (g₀,x₀) contMDiffAt_snd
  exact hto'.clm_comp (hpartial.clm_comp hfrom')

end
end QuaternionicSymmetry.ManifoldQuaternionicFullMovingAdaptedSmooth
