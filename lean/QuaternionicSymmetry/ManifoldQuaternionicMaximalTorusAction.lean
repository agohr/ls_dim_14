import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorus
import QuaternionicSymmetry.ManifoldQuaternionicTorusAction

/-! A maximal torus in the actual quaternionic-isometry group supplies the
same faithful continuous torus action consumed by the fixed-weight and
contact-power constructions. Maximality is retained at the group level. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusAction

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [LocallyCompactSpace M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The action of a genuine torus embedding uses exactly its homomorphism,
not a new or merely isomorphic torus representation. -/
def actionOfEmbedding {r : ℕ}
    (T : TorusEmbedding (QuaternionicIsometries Q) r) :
    ContinuousTorusAction Q r where
  representation := T.hom
  continuous_action :=
    (ManifoldQuaternionicIsometryTopology.continuous_action Q).comp
      ((T.continuous_hom.comp continuous_fst).prodMk continuous_snd)

theorem actionOfEmbedding_representation {r : ℕ}
    (T : TorusEmbedding (QuaternionicIsometries Q) r) :
    (actionOfEmbedding Q T).representation = T.hom := rfl

theorem actionOfEmbedding_faithful {r : ℕ}
    (T : TorusEmbedding (QuaternionicIsometries Q) r) :
    (actionOfEmbedding Q T).Faithful := T.injective_hom

/-- Retain both the maximal subgroup and its exact faithful action. -/
theorem exists_action_of_maximal_embedding {r : ℕ}
    (T : TorusEmbedding (QuaternionicIsometries Q) r)
    (hMax : T.IsMaximal (QuaternionicIsometries Q)) :
    ∃ A : ContinuousTorusAction Q r,
      A.Faithful ∧ A.representation = T.hom ∧
        A.imageSubgroup = T.hom.range ∧
          ∀ S : Subgroup (QuaternionicIsometries Q),
            IsTorusSubgroup (QuaternionicIsometries Q) S →
            A.imageSubgroup ≤ S → S = A.imageSubgroup := by
  refine ⟨actionOfEmbedding Q T, actionOfEmbedding_faithful Q T,
    rfl, rfl, ?_⟩
  exact hMax

end
end QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusAction
