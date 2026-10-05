import QuaternionicSymmetry.ManifoldQuaternionicConstructedScalarPositive
import QuaternionicSymmetry.ManifoldQuaternionicTangentSpanInFrame

/-! The constructed tangent metric and quaternionic span are exactly the
ones induced by the genuine inclusion derivative. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicConstructedIdentification
open ManifoldQuaternionicInducedConnectionConstruction ManifoldQuaternionicTangentSpanInFrame
open ManifoldQuaternionicConnection ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicImmersionCharts ManifoldQuaternionicInducedTotalGeodesy
open ManifoldQuaternionicInducedLocalIntertwining ManifoldQuaternionicSpanSymmetry
open ManifoldPositiveQuaternionicKahlerGeometry
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable {P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)}
  {Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,F)) (M := N) (n := ∞)} {ι : N → M}
  (L : LocalFrames P Q ι)

theorem center_target (x : N) : ι x ∈ (chartAt E (L.ambientPoint x)).source := by
  have h := L.target x ((extChartAt 𝓘(ℝ,F) x) x)
    ((extChartAt 𝓘(ℝ,F) x).map_source (mem_extChartAt_source x))
  simpa only [(extChartAt 𝓘(ℝ,F) x).left_inv (mem_extChartAt_source x),extChartAt_source] using h

def sourceFrame (x : N) : F ≃L[ℝ] F := inFrame Q (achart F x) x (mem_chart_source F x)
def targetFrame (x : N) : E ≃L[ℝ] E :=
  inFrame P.tangent (achart E (L.ambientPoint x)) (ι x) (center_target L x)
def centerEmbedding (x : N) : F →L[ℝ] E := L.embedding x ((extChartAt 𝓘(ℝ,F) x) x)

theorem sourceFrame_apply (x : N) (v : F) :
    sourceFrame (Q := Q) x v = Q.frames.toFrame (achart F x) x v := by
  change Q.frames.toFrame _ _ ((tangentBundleCore 𝓘(ℝ,F) N).coordChange (achart F x) (achart F x) x v) = _
  rw [(tangentBundleCore 𝓘(ℝ,F) N).coordChange_self _ _ (mem_chart_source F x)]

theorem frame_inclusion (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι) (x : N) (v : F) :
    centerEmbedding L x (sourceFrame (Q := Q) x v) =
      targetFrame L x (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) := by
  let y := (extChartAt 𝓘(ℝ,F) x) x
  have hy : y ∈ (extChartAt 𝓘(ℝ,F) x).target :=
    (extChartAt 𝓘(ℝ,F) x).map_source (mem_extChartAt_source x)
  have hx : (extChartAt 𝓘(ℝ,F) x).symm y = x :=
    (extChartAt 𝓘(ℝ,F) x).left_inv (mem_extChartAt_source x)
  have ht := L.target x y hy
  have hfy := (extChartAt 𝓘(ℝ,E) (L.ambientPoint x)).map_source ht
  have he := L.solder_eq x y hy
  rw [LocalSolderPullback.solder,solder_eq_toFrame Q x y hy,
    localBaseMap_fderiv ι hι x (L.ambientPoint x) y ⟨hy,ht⟩] at he
  dsimp only [localBaseMap] at he
  rw [solder_eq_toFrame P.tangent (L.ambientPoint x) _ hfy,
    (extChartAt 𝓘(ℝ,E) (L.ambientPoint x)).left_inv ht,hx] at he
  have hev := congrArg (fun A : F →L[ℝ] E => A v) he
  rw [sourceFrame_apply]
  change _ = P.tangent.frames.toFrame _ _
    ((tangentBundleCore 𝓘(ℝ,E) M).coordChange (achart E (ι x)) (achart E (L.ambientPoint x)) (ι x)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v))
  change centerEmbedding L x (Q.frames.toFrame (achart F x) x v) =
    P.tangent.frames.toFrame _ _ ((tangentBundleCore 𝓘(ℝ,E) M).coordChange _ _ _
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
        ((tangentBundleCore 𝓘(ℝ,F) N).coordChange (achart F x) (achart F x) x v))) at hev
  rw [(tangentBundleCore 𝓘(ℝ,F) N).coordChange_self _ _ (mem_chart_source F x)] at hev
  exact hev

include L

theorem metric_induced (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι) (x : N) (v w : F) :
    Q.tangentMetricForm x v w = P.tangent.tangentMetricForm (ι x)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x w) := by
  rw [P.tangent.tangentMetric_chart_eq (achart E (L.ambientPoint x)) (ι x) (center_target L x)]
  change inner ℝ (Q.frames.toFrame (achart F x) x v) (Q.frames.toFrame (achart F x) x w) =
    inner ℝ (targetFrame L x _) (targetFrame L x _)
  rw [← frame_inclusion L hι,← frame_inclusion L hι]
  unfold centerEmbedding
  rw [L.inner_embedding x _ ((extChartAt 𝓘(ℝ,F) x).map_source (mem_extChartAt_source x))]
  rw [sourceFrame_apply,sourceFrame_apply]

theorem span_induced (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι) (x : N) (A : F →L[ℝ] F) :
    A ∈ tangentSpan Q x ↔ ∃ C ∈ tangentSpan P.tangent (ι x), ∀ v,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (A v) = C (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) := by
  let s := sourceFrame (Q := Q) x
  let t := targetFrame L x
  let B := centerEmbedding L x
  have hy := (extChartAt 𝓘(ℝ,F) x).map_source (mem_extChartAt_source x)
  have hB : Function.Injective B := by
    intro v w h
    have he := congrArg B.adjoint h
    simpa only [QuaternionicRangeFrameCoordinates.adjoint_left_inverse B (L.inner_embedding x _ hy)] using he
  have heq := QuaternionicFrameInjectionSpan.mem_span_iff
    (Q.reduction.Q (achart F x)) (P.tangent.reduction.Q (achart E (L.ambientPoint x))) B
    (L.intertwines_I x _ hy) (L.intertwines_J x _ hy) hB
    (toFrameOperator Q (achart F x) x (mem_chart_source F x) A)
  rw [ManifoldQuaternionicTangentSpanInFrame.mem_span_iff Q (achart F x) x (mem_chart_source F x),heq]
  constructor
  · rintro ⟨C,hC,hAC⟩
    let C' : E →L[ℝ] E := (t.symm.toContinuousLinearMap.comp C).comp t.toContinuousLinearMap
    refine ⟨C',?_,?_⟩
    · rw [ManifoldQuaternionicTangentSpanInFrame.mem_span_iff P.tangent (achart E (L.ambientPoint x)) (ι x) (center_target L x)]
      have he : toFrameOperator P.tangent (achart E (L.ambientPoint x)) (ι x) (center_target L x) C' = C := by
        ext v
        change t (t.symm (C (t (t.symm v)))) = C v
        rw [t.apply_symm_apply,t.apply_symm_apply]
      rw [he]
      exact hC
    · intro v
      apply t.injective
      have h := hAC (s v)
      change B (s (A (s.symm (s v)))) = C (B (s v)) at h
      rw [s.symm_apply_apply,frame_inclusion L hι,frame_inclusion L hι] at h
      change t (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (A v)) = t (t.symm (C (t _)))
      rw [t.apply_symm_apply]
      exact h
  · rintro ⟨C,hC,hAC⟩
    refine ⟨toFrameOperator P.tangent (achart E (L.ambientPoint x)) (ι x) (center_target L x) C,
      (ManifoldQuaternionicTangentSpanInFrame.mem_span_iff P.tangent (achart E (L.ambientPoint x)) (ι x) (center_target L x) C).mp hC,?_⟩
    intro v
    change B (s (A (s.symm v))) = t (C (t.symm (B v)))
    rw [frame_inclusion L hι,hAC]
    congr 2
    apply t.injective
    rw [t.apply_symm_apply,← frame_inclusion L hι]
    exact congrArg B (s.apply_symm_apply v)

end
end QuaternionicSymmetry.ManifoldQuaternionicConstructedIdentification
