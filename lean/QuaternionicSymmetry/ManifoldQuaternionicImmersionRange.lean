import QuaternionicSymmetry.ManifoldImmersionFixedDerivativeSmooth
import QuaternionicSymmetry.ManifoldQuaternionicSubmanifoldInput

/-! Express the genuine inclusion derivative in a fixed ambient adapted
frame. Its image is quaternionic invariant before constructing any source
quaternionic geometry. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicImmersionRange
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldImmersionFixedDerivativeSmooth
open ManifoldQuaternionicSubmanifoldInput
open ManifoldPositiveQuaternionicKahlerGeometry
open VectorBundleFrameTransitions
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)) (ι : N → M)

def adaptedDerivative (i : atlas F N) (j : atlas E M) (x : N) : F →L[ℝ] E :=
  (P.tangent.frames.toFrame j (ι x)).comp (localDerivative ι i j x)

theorem adaptedDerivative_contMDiffAt
    (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
    (i : atlas F N) (j : atlas E M) (x : N)
    (hi : x ∈ i.1.source) (hj : ι x ∈ j.1.source) :
    ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞ (adaptedDerivative P ι i j) x :=
  (((P.tangent.frames.smooth_to j).contMDiffAt
    (j.1.open_source.mem_nhds hj)).comp x hι.contMDiffAt).clm_comp
      (localDerivative_contMDiffAt ι hι i j x hi hj)

theorem adaptedDerivative_injective
    (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
    (i : atlas F N) (j : atlas E M) (x : N)
    (hi : x ∈ i.1.source) (hj : ι x ∈ j.1.source) :
    Function.Injective (adaptedDerivative P ι i j x) := by
  let Z := tangentBundleCore 𝓘(ℝ,F) N
  let T := tangentBundleCore 𝓘(ℝ,E) M
  have hinvN (v : F) : Z.coordChange (achart F x) i x
      (Z.coordChange i (achart F x) x v) = v := by
    rw [Z.coordChange_comp i (achart F x) i x ⟨⟨hi,mem_chart_source F x⟩,hi⟩,
      Z.coordChange_self i x hi]
  have hinvM (v : E) : T.coordChange j (achart E (ι x)) (ι x)
      (T.coordChange (achart E (ι x)) j (ι x) v) = v := by
    rw [T.coordChange_comp (achart E (ι x)) j (achart E (ι x)) (ι x)
      ⟨⟨mem_chart_source E (ι x),hj⟩,mem_chart_source E (ι x)⟩,
      T.coordChange_self _ _ (mem_chart_source E (ι x))]
  intro v w h
  have h₁ := congrArg (P.tangent.frames.fromFrame j (ι x)) h
  change P.tangent.frames.fromFrame j (ι x) (P.tangent.frames.toFrame j (ι x) _) =
    P.tangent.frames.fromFrame j (ι x) (P.tangent.frames.toFrame j (ι x) _) at h₁
  rw [P.tangent.frames.from_to j (ι x) hj,P.tangent.frames.from_to j (ι x) hj] at h₁
  have h₂ := congrArg (T.coordChange j (achart E (ι x)) (ι x)) h₁
  change T.coordChange j (achart E (ι x)) (ι x)
      (T.coordChange (achart E (ι x)) j (ι x) _) =
    T.coordChange j (achart E (ι x)) (ι x)
      (T.coordChange (achart E (ι x)) j (ι x) _) at h₂
  rw [hinvM,hinvM] at h₂
  have h₃ := congrArg (Z.coordChange (achart F x) i x) (hι x h₂)
  exact (hinvN v).symm.trans (h₃.trans (hinvN w))

theorem adaptedDerivative_range_generator
    (hQ : QuaternionicTangentRange (F := F) P ι)
    (i : atlas F N) (j : atlas E M) (x : N)
    (hi : x ∈ i.1.source) (hj : ι x ∈ j.1.source) (t : Fin 3)
    (z : E) (hz : z ∈ LinearMap.range (adaptedDerivative P ι i j x).toLinearMap) :
    quaternionicGenerator (P.tangent.reduction.Q j) t z ∈
      LinearMap.range (adaptedDerivative P ι i j x).toLinearMap := by
  obtain ⟨v,rfl⟩ := hz
  let Z := tangentBundleCore 𝓘(ℝ,F) N
  let T := tangentBundleCore 𝓘(ℝ,E) M
  let k := achart E (ι x)
  let d := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
  let G := (transitionAtlas T).adjointCoordChange j k (ι x)
    (P.tangent.chartGenerator j t (ι x))
  have hG : G ∈ ManifoldQuaternionicSpanSymmetry.tangentSpan P.tangent (ι x) :=
    P.tangent.tangent_generator_transport j k (ι x) hj (mem_chart_source E (ι x)) t
  have hmem := hQ x G hG (d (Z.coordChange i (achart F x) x v))
    ⟨Z.coordChange i (achart F x) x v,rfl⟩
  obtain ⟨w,hw⟩ := hmem
  refine ⟨Z.coordChange (achart F x) i x w,?_⟩
  have hinvN : Z.coordChange i (achart F x) x
      (Z.coordChange (achart F x) i x w) = w := by
    rw [Z.coordChange_comp (achart F x) i (achart F x) x
      ⟨⟨mem_chart_source F x,hi⟩,mem_chart_source F x⟩,
      Z.coordChange_self _ _ (mem_chart_source F x)]
  change P.tangent.frames.toFrame j (ι x)
    (T.coordChange k j (ι x) (d (Z.coordChange i (achart F x) x
      (Z.coordChange (achart F x) i x w)))) = _
  rw [hinvN]
  change d w = G (d (Z.coordChange i (achart F x) x v)) at hw
  rw [hw]
  change P.tangent.frames.toFrame j (ι x)
    (T.coordChange k j (ι x) (T.coordChange j k (ι x)
      (P.tangent.chartGenerator j t (ι x)
        (T.coordChange k j (ι x) (d (Z.coordChange i (achart F x) x v)))))) = _
  rw [T.coordChange_comp j k j (ι x) ⟨⟨hj,mem_chart_source E (ι x)⟩,hj⟩,
    T.coordChange_self j (ι x) hj]
  exact P.tangent.frames.to_from j (ι x) hj _

theorem adaptedDerivative_coordChange
    (i i' : atlas F N) (j j' : atlas E M) (x : N)
    (hi : x ∈ i.1.source) (hi' : x ∈ i'.1.source)
    (hj : ι x ∈ j.1.source) (hj' : ι x ∈ j'.1.source) (v : F) :
    adaptedDerivative P ι i' j' x
      ((tangentBundleCore 𝓘(ℝ,F) N).coordChange i i' x v) =
    P.tangent.frames.coordChange j j' (ι x) (adaptedDerivative P ι i j x v) := by
  let Z := tangentBundleCore 𝓘(ℝ,F) N
  let T := tangentBundleCore 𝓘(ℝ,E) M
  change P.tangent.frames.toFrame j' (ι x)
    (T.coordChange (achart E (ι x)) j' (ι x)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
        (Z.coordChange i' (achart F x) x (Z.coordChange i i' x v)))) =
    P.tangent.frames.toFrame j' (ι x)
      (T.coordChange j j' (ι x)
        (P.tangent.frames.fromFrame j (ι x) (P.tangent.frames.toFrame j (ι x)
          (T.coordChange (achart E (ι x)) j (ι x)
            (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (Z.coordChange i (achart F x) x v))))))
  rw [P.tangent.frames.from_to j (ι x) hj,
    Z.coordChange_comp i i' (achart F x) x ⟨⟨hi,hi'⟩,mem_chart_source F x⟩,
    T.coordChange_comp (achart E (ι x)) j j' (ι x)
      ⟨⟨mem_chart_source E (ι x),hj⟩,hj'⟩]

end
end QuaternionicSymmetry.ManifoldQuaternionicImmersionRange
