import QuaternionicSymmetry.ComplexIdentityComponentTangentIdentity
import QuaternionicSymmetry.ComplexGroupLieBracketRestriction

/-! In the inherited identity-component chart, the genuine complex
tangent Lie bracket agrees with that of the full group. This follows by
differentiating the actual inclusion homomorphism, not by assigning a
replacement bracket to either tangent space. -/

namespace QuaternionicSymmetry.ComplexIdentityComponentLieBracket

open IdentityComponentLie ComplexLieRealCompanion
open ManifoldComplexHolomorphicFactorization
open ComplexGroupLieBracketRestriction SmoothLieHomDerivativeBracket
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace V G] [IsManifold 𝓘(ℂ,V) ∞ G] [LieGroup 𝓘(ℂ,V) ∞ G]

local instance realMin : ENat.LEInfty (minSmoothness ℝ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem component_bracket_eq_full (v w : V) :
    letI : ChartedSpace V (Component G) := ComplexIdentityComponentLie.charts V G
    @Bracket.bracket (GroupLieAlgebra 𝓘(ℂ,V) (Component G))
      (GroupLieAlgebra 𝓘(ℂ,V) (Component G)) inferInstance v w =
      @Bracket.bracket (GroupLieAlgebra 𝓘(ℂ,V) G)
        (GroupLieAlgebra 𝓘(ℂ,V) G) inferInstance v w := by
  letI : ChartedSpace V (Component G) := ComplexIdentityComponentLie.charts V G
  letI : IsManifold 𝓘(ℂ,V) ∞ (Component G) :=
    ComplexIdentityComponentLie.manifold V G
  letI : LieGroup 𝓘(ℂ,V) ∞ (Component G) :=
    ComplexIdentityComponentLie.lieGroup V G
  letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ G := realLieGroup
  letI : IsManifold 𝓘(ℝ,V) ∞ (Component G) := realManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (Component G) := realLieGroup
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hInc : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ (Component G).subtype :=
    holomorphic_is_real_smooth (ComplexIdentityComponentLie.inclusion_holomorphic V G)
  have h := mfderiv_map_lie (Component G).subtype hInc v w
  have hId : mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (Component G).subtype 1 =
      ContinuousLinearMap.id ℝ V :=
    ComplexIdentityComponentTangentIdentity.inclusion_mfderiv_eq_id 1
  rw [hId] at h
  change @Bracket.bracket (GroupLieAlgebra 𝓘(ℝ,V) (Component G))
    (GroupLieAlgebra 𝓘(ℝ,V) (Component G)) inferInstance v w =
    @Bracket.bracket (GroupLieAlgebra 𝓘(ℝ,V) G)
      (GroupLieAlgebra 𝓘(ℝ,V) G) inferInstance v w at h
  rw [bracket_real_eq_complex (V := V) (K := Component G),
    bracket_real_eq_complex (V := V) (K := G)] at h
  exact h

end
end QuaternionicSymmetry.ComplexIdentityComponentLieBracket
