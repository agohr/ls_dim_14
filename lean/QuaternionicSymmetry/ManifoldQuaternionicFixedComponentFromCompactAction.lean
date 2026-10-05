import QuaternionicSymmetry.CompactSubgroupFixedComponent
import QuaternionicSymmetry.ManifoldQuaternionicIsometryClosedFromAction
import QuaternionicSymmetry.ManifoldRiemannianFixedComponentInput

/-! On compact connected bases, the quaternionic fixed-component theorem is
proved by compact-action averaging and the already retained Lie sources. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedComponentFromCompactAction
open ManifoldQuaternionicSpanSymmetry ManifoldRiemannianFixedComponentInput
open ManifoldQuaternionicFixedTangentDimension
open ManifoldQuaternionicIsometryClosedSubgroup
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [PreconnectedSpace M] [Nonempty M]

lemma fixedComponents
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hLee : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem) :
    RiemannianFixedComponentOnModel (E := E) (M := M) := by
  intro _ _ _ _ _ Q S x hx
  letI : T3Space M := inferInstance
  letI : CompactSpace (QuaternionicIsometries Q) :=
    quaternionicIsometries_compactSpace_of_isometryLie Q (hR3 Q)
  obtain ⟨d,c,hm,hl,ha⟩ := exists_quaternionic_lie_atlas_of_isometryLie Q (hR3 Q) hLee
  letI := c
  letI := hm
  letI := hl
  letI : T2Space (QuaternionicIsometries Q) := by infer_instance
  letI : SecondCountableTopology (QuaternionicIsometries Q) :=
    ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℝ) (QuaternionicIsometries Q)
  obtain ⟨k,⟨A⟩⟩ := CompactSubgroupFixedComponent.exists_atlas hLee
    (fun p : QuaternionicIsometries Q × M => p.1 • p.2) ha
    (fun y => one_smul _ y) (fun g h y => (mul_smul g h y).symm) S x hx
  refine ⟨k,⟨⟨A.charts,A.manifold,A.inclusion_smooth,A.inclusion_injective_derivative,?_⟩⟩⟩
  intro y
  ext v
  exact A.tangent_eq y v

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedComponentFromCompactAction
