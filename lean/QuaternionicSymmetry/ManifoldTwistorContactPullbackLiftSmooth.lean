import QuaternionicSymmetry.ManifoldTwistorContactHorizontalLift

/-! Smoothness of the canonical map from the smooth pullback bundle π*TM
to the genuine tangent bundle TM. This map preserves the tangent vector
and changes only its base from a twistor point to its projection. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open Bundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev J := ((𝓘(ℝ,E)).prod (𝓡 2)).prod 𝓘(ℝ,E)

set_option maxHeartbeats 800000 in

theorem contactPullbackLift_smooth :
    ContMDiff (J (E := E)) (𝓘(ℝ,E)).tangent ∞
      (Pullback.lift (twistorProjectionMap Q) :
        Bundle.TotalSpace E (contactPullbackFiber Q) →
          TangentBundle 𝓘(ℝ,E) M) := by
  intro t
  let x := (twistorProjectionMap Q) t.1
  let e := FiberBundle.trivializationAt E
    (TangentSpace 𝓘(ℝ,E) : M → Type _) x
  let e' := e.pullback (twistorProjectionMap Q)
  haveI : MemTrivializationAtlas e := inferInstance
  haveI : MemTrivializationAtlas e' := ⟨⟨e, inferInstance, rfl⟩⟩
  have he : Pullback.lift (twistorProjectionMap Q) t ∈ e.source := by
    change x ∈ e.baseSet
    exact FiberBundle.mem_baseSet_trivializationAt E
      (TangentSpace 𝓘(ℝ,E) : M → Type _) x
  rw [e.contMDiffAt_iff he]
  constructor
  · exact (twistorProjectionMap Q).contMDiff.contMDiffAt.comp t
      ((Bundle.contMDiff_proj (contactPullbackFiber Q)).contMDiffAt)
  · have ht : t ∈ e'.source := by
      change Pullback.lift (twistorProjectionMap Q) t ∈ e.source
      exact he
    letI : ContMDiffVectorBundle ∞ E (contactPullbackFiber Q) (I (E := E)) :=
      contactPullbackSmoothBundle Q
    have hs0 : ContMDiffOn (J (E := E)) (J (E := E)) ∞ e' e'.source :=
      e'.contMDiffOn
    have hs := hs0.contMDiffAt (e'.open_source.mem_nhds ht)
    exact hs.snd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => rfl))

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
