import QuaternionicSymmetry.ManifoldQuaternionicSpanSymmetry

/-! Exact identification of the genuine tangent quaternionic span in any
valid adapted orthonormal chart. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicTangentSpanInFrame
open ManifoldQuaternionicSpanSymmetry VectorBundleFrameTransitions
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def inFrame (i : atlas E M) (x : M) (hi : x ∈ i.1.source) : E ≃L[ℝ] E where
  toLinearEquiv := {
    toLinearMap := ((Q.frames.toFrame i x).comp
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange (achart E x) i x)).toLinearMap
    invFun := fun v => (tangentBundleCore 𝓘(ℝ,E) M).coordChange i (achart E x) x (Q.frames.fromFrame i x v)
    left_inv := by
      intro v
      change (tangentBundleCore 𝓘(ℝ,E) M).coordChange i (achart E x) x
        (Q.frames.fromFrame i x (Q.frames.toFrame i x
          ((tangentBundleCore 𝓘(ℝ,E) M).coordChange (achart E x) i x v))) = v
      rw [Q.frames.from_to i x hi,
        (tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp (achart E x) i (achart E x) x
          ⟨⟨mem_chart_source E x,hi⟩,mem_chart_source E x⟩,
        (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self _ _ (mem_chart_source E x)]
    right_inv := by
      intro v
      change Q.frames.toFrame i x ((tangentBundleCore 𝓘(ℝ,E) M).coordChange (achart E x) i x
        ((tangentBundleCore 𝓘(ℝ,E) M).coordChange i (achart E x) x (Q.frames.fromFrame i x v))) = v
      rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp i (achart E x) i x
        ⟨⟨hi,mem_chart_source E x⟩,hi⟩,
        (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self _ _ hi,Q.frames.to_from i x hi] }
  continuous_toFun := ((Q.frames.toFrame i x).comp _).continuous
  continuous_invFun := (((tangentBundleCore 𝓘(ℝ,E) M).coordChange i (achart E x) x).comp
    (Q.frames.fromFrame i x)).continuous

def toFrameOperator (i : atlas E M) (x : M) (hi : x ∈ i.1.source) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  ((inFrame Q i x hi).toContinuousLinearMap.comp A).comp
    (inFrame Q i x hi).symm.toContinuousLinearMap

theorem mem_span_iff (i : atlas E M) (x : M) (hi : x ∈ i.1.source) (A : E →L[ℝ] E) :
    A ∈ tangentSpan Q x ↔ toFrameOperator Q i x hi A ∈ quaternionicSpan (Q.reduction.Q i) := by
  let k := achart E x
  let C := tangentBundleCore 𝓘(ℝ,E) M
  have hk : x ∈ C.baseSet k := mem_chart_source E x
  have hspan : tangentSpan Q x = Submodule.map
      (((transitionAtlas C).adjointCoordChange i k x).toLinearMap.comp (Q.chartConjugation i x).toLinearMap)
      (quaternionicSpan (Q.reduction.Q i)) := by
    change Q.chartSpan k x = _
    rw [← Q.tangent_map_chartSpan_eq i k x hi hk,Q.chartSpan_eq_map,Submodule.map_comp]
  have he (a : E →L[ℝ] E) (v : E) :
      (transitionAtlas C).adjointCoordChange i k x (Q.chartConjugation i x a) v =
        (inFrame Q i x hi).symm (a (inFrame Q i x hi v)) := rfl
  rw [hspan]
  constructor
  · rintro ⟨a,ha,hA⟩
    have ha' : toFrameOperator Q i x hi A = a := by
      rw [← hA]
      ext v
      change inFrame Q i x hi
        ((transitionAtlas C).adjointCoordChange i k x (Q.chartConjugation i x a)
          ((inFrame Q i x hi).symm v)) = a v
      rw [he,ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]
    rw [ha']
    exact ha
  · intro hA
    refine ⟨toFrameOperator Q i x hi A,hA,?_⟩
    ext v
    change (transitionAtlas C).adjointCoordChange i k x
      (Q.chartConjugation i x (toFrameOperator Q i x hi A)) v = A v
    rw [he]
    change (inFrame Q i x hi).symm (inFrame Q i x hi
      (A ((inFrame Q i x hi).symm (inFrame Q i x hi v)))) = A v
    rw [ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearEquiv.symm_apply_apply]

end
end QuaternionicSymmetry.ManifoldQuaternionicTangentSpanInFrame
