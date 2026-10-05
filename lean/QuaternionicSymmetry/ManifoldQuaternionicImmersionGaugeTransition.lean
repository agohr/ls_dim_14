import QuaternionicSymmetry.ManifoldQuaternionicImmersionGaugeAtlas
import QuaternionicSymmetry.QuaternionicFrameInjectionSpan

/-! The induced local gauges glue by the genuine tangent transition maps.
Their transition maps are orthogonal and preserve quaternionic spans. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicImmersionGaugeTransition
open ManifoldQuaternionicImmersionLocalGauge ManifoldQuaternionicImmersionRange
open ManifoldPositiveQuaternionicKahlerGeometry QuaternionicFrameInjectionSpan
open VectorBundleFrameTransitions
open scoped Manifold ContDiff
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable {P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)} {ι : N → M}
  (G : ∀ c, LocalGauge (F := F) P ι c)

def transition (c d x : N) : F →L[ℝ] F :=
  ((G d).toFrame x).comp (((tangentBundleCore 𝓘(ℝ,F) N).coordChange
    (achart F c) (achart F d) x).comp ((G c).fromFrame x))

theorem embedding_transition (c d x : N)
    (hc : x ∈ (G c).domain) (hd : x ∈ (G d).domain) (v : F) :
    (G d).embedding x (transition G c d x v) =
      P.tangent.frames.coordChange (achart E (ι c)) (achart E (ι d)) (ι x)
        ((G c).embedding x v) := by
  change (G d).embedding x ((G d).toFrame x _) = _
  rw [(G d).inclusion x hd]
  change adaptedDerivative P ι (achart F d) (achart E (ι d)) x
    ((tangentBundleCore 𝓘(ℝ,F) N).coordChange (achart F c) (achart F d) x ((G c).fromFrame x v)) = _
  rw [adaptedDerivative_coordChange P ι (achart F c) (achart F d)
    (achart E (ι c)) (achart E (ι d)) x ((G c).source hc) ((G d).source hd)
      ((G c).target hc) ((G d).target hd)]
  rw [← (G c).inclusion x hc,(G c).to_from x hc]

theorem transition_inner (c d x : N)
    (hc : x ∈ (G c).domain) (hd : x ∈ (G d).domain) (v w : F) :
    inner ℝ (transition G c d x v) (transition G c d x w) = inner ℝ v w := by
  rw [← (G d).inner_embedding x hd,embedding_transition G c d x hc hd,
    embedding_transition G c d x hc hd,
    P.tangent.transition_inner (achart E (ι c)) (achart E (ι d)) (ι x)
      ((G c).target hc) ((G d).target hd), (G c).inner_embedding x hc]

theorem generator_transition (c d x : N)
    (hc : x ∈ (G c).domain) (hd : x ∈ (G d).domain) (t : Fin 3) :
    (transition G c d x).comp ((quaternionicGenerator (G c).Q t).comp
      (transition G d c x)) ∈ quaternionicSpan (G d).Q := by
  let jc := achart E (ι c)
  let jd := achart E (ι d)
  let A := (transitionAtlas P.tangent.frames.adaptedCore).adjointCoordChange jc jd (ι x)
    (quaternionicGenerator (P.tangent.reduction.Q jc) t)
  have hA : A ∈ quaternionicSpan (P.tangent.reduction.Q jd) :=
    P.tangent.reduction.generator_transport jc jd (ι x) ((G c).target hc) ((G d).target hd) t
  have hinj : Function.Injective ((G d).embedding x) :=
    Function.LeftInverse.injective (QuaternionicRangeFrameCoordinates.adjoint_left_inverse
      ((G d).embedding x) ((G d).inner_embedding x hd))
  apply (mem_span_iff (G d).Q (P.tangent.reduction.Q jd) ((G d).embedding x)
    ((G d).intertwines_I x hd) ((G d).intertwines_J x hd) hinj _).mpr
  refine ⟨A,hA,?_⟩
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  rw [embedding_transition G c d x hc hd]
  rw [generator_intertwines (G c).Q (P.tangent.reduction.Q jc) ((G c).embedding x)
    ((G c).intertwines_I x hc) ((G c).intertwines_J x hc)]
  rw [embedding_transition G d c x hd hc]
  rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicImmersionGaugeTransition
