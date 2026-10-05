import QuaternionicSymmetry.OpenSubgroupLieTangentIdentity
import QuaternionicSymmetry.IdentityComponentLie
import QuaternionicSymmetry.SmoothLieHomDerivativeBracket

/-! The inherited open identity-component chart has the SAME tangent
Lie bracket as the full group: the actual subgroup inclusion has identity
derivative and smooth-hom derivative preserves the bracket. -/

namespace QuaternionicSymmetry.IdentityComponentLieBracketAgreement

open IdentityComponentLie OpenSubgroupLieTangentIdentity
open SmoothLieHomDerivativeBracket
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V] [ENat.LEInfty (minSmoothness ℝ 3)]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace V G] [LieGroup 𝓘(ℝ,V) ∞ G]

theorem component_bracket_eq_full (x y : V) :
    letI := IdentityComponentLie.charts V G
    letI := IdentityComponentLie.lieGroup V G
    @Bracket.bracket (GroupLieAlgebra 𝓘(ℝ,V) (Component G))
      (GroupLieAlgebra 𝓘(ℝ,V) (Component G)) inferInstance x y =
    @Bracket.bracket (GroupLieAlgebra 𝓘(ℝ,V) G)
      (GroupLieAlgebra 𝓘(ℝ,V) G) inferInstance x y := by
  letI := IdentityComponentLie.charts V G
  letI := IdentityComponentLie.lieGroup V G
  have h := mfderiv_map_lie
    ((Component G).subtype : Component G →* G)
    (IdentityComponentLie.inclusion_smooth V G) x y
  change (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V)
    (Subtype.val : Component G → G) 1)
      (@Bracket.bracket (GroupLieAlgebra 𝓘(ℝ,V) (Component G))
        (GroupLieAlgebra 𝓘(ℝ,V) (Component G)) inferInstance x y) =
      @Bracket.bracket (GroupLieAlgebra 𝓘(ℝ,V) G)
        (GroupLieAlgebra 𝓘(ℝ,V) G) inferInstance
        ((mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V)
          (Subtype.val : Component G → G) 1) x)
        ((mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V)
          (Subtype.val : Component G → G) 1) y) at h
  simpa only [mfderiv_inclusion_one_eq_id (Component G)
    (IdentityComponentLie.isOpen_component V G),
    ContinuousLinearMap.id_apply] using h

end
end QuaternionicSymmetry.IdentityComponentLieBracketAgreement
