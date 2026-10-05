import QuaternionicSymmetry.ManifoldQuaternionicImmersionHermitianTangent
import QuaternionicSymmetry.ManifoldTangentFrameMetricIdentification

/-! The constructed quaternionic Hermitian tangent metric is exactly the
pullback through the genuine immersion derivative. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicImmersionMetricIdentification
open ManifoldQuaternionicImmersionLocalGauge ManifoldQuaternionicImmersionGaugeAtlas
open ManifoldQuaternionicImmersionRange ManifoldQuaternionicImmersionHermitianTangent
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicMetric
open ManifoldTangentFrameMetricIdentification
open scoped Manifold ContDiff
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [old : ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable {P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)} {ι : N → M}
  (G : ∀ c, LocalGauge (F := F) P ι c)

theorem local_metric (c x : N) (hx : x ∈ (G c).domain) (v w : F) :
    P.tangent.tangentMetricForm (ι x)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
        ((tangentBundleCore 𝓘(ℝ,F) N).coordChange (achart F c) (achart F x) x ((G c).fromFrame x v)))
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
        ((tangentBundleCore 𝓘(ℝ,F) N).coordChange (achart F c) (achart F x) x ((G c).fromFrame x w))) =
      inner ℝ v w := by
  rw [P.tangent.tangentMetric_chart_eq (achart E (ι c)) (ι x) ((G c).target hx)]
  change inner ℝ
    (adaptedDerivative P ι (achart F c) (achart E (ι c)) x ((G c).fromFrame x v))
    (adaptedDerivative P ι (achart F c) (achart E (ι c)) x ((G c).fromFrame x w)) = _
  rw [← (G c).inclusion x hx,← (G c).inclusion x hx,
    (G c).to_from x hx,(G c).to_from x hx,(G c).inner_embedding x hx]

theorem metric_eq_original_derivative (x : N) (v w : F) :
    let d := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
    letI := charts G
    letI := charts_manifold (old := old) G
    (tangent (old := old) G).tangentMetricForm x v w =
      P.tangent.tangentMetricForm (ι x) (d v) (d w) := by
  let d := fun y => mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι y
  let g : N → F → F → ℝ := fun y a b => P.tangent.tangentMetricForm (ι y) (d y a) (d y b)
  have hlocal (i : Index G) (y : N) (hy : y ∈ i.1.source) (a b : F) :
      letI := charts G
      letI := charts_manifold (old := old) G
      g y
        ((tangentBundleCore 𝓘(ℝ,F) N).coordChange i (achart F y) y
          ((frames (old := old) G).fromFrame i y a))
        ((tangentBundleCore 𝓘(ℝ,F) N).coordChange i (achart F y) y
          ((frames (old := old) G).fromFrame i y b)) = inner ℝ a b := by
    have hC := coreTransition_to_preferred G i y
    have h := local_metric G (chartCenter G i) y (mem_domain G i y hy) a b
    letI := charts G
    letI := charts_manifold (old := old) G
    rw [hC]
    exact h
  letI := charts G
  letI := charts_manifold (old := old) G
  exact (preferred_frame_metric_eq (frames (old := old) G) g hlocal x v w).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicImmersionMetricIdentification
