import QuaternionicSymmetry.ComplexGroupLieBracketRestriction

/-! Tangents to an actual smoothly embedded centralizer centralize the
derivative of the selected compact subgroup. This uses the genuine complex
Lie bracket on the target; no coordinate or dimension surrogate appears. -/

namespace QuaternionicSymmetry.ComplexLieCentralizerTangent

open QuaternionicSymmetry.ComplexGroupLieBracketRestriction
open scoped Manifold ContDiff
noncomputable section

variable {E F V G K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Group K] [TopologicalSpace K] [ChartedSpace V K]
  [IsManifold 𝓘(ℂ,V) ∞ K] [LieGroup 𝓘(ℂ,V) ∞ K]
  [IsManifold 𝓘(ℝ,V) ∞ K] [LieGroup 𝓘(ℝ,V) ∞ K]

local instance realMin : ENat.LEInfty (minSmoothness ℝ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem centralizer_derivative_bracket_zero
    (H : Subgroup K)
    [ChartedSpace F H] [IsManifold 𝓘(ℝ,F) ∞ H]
    [LieGroup 𝓘(ℝ,F) ∞ H]
    (h : G →* K)
    (hH : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ H.subtype)
    (hh : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ h)
    (hComm : ∀ (a : H) (b : G), Commute (a : K) (h b))
    (u : GroupLieAlgebra 𝓘(ℝ,F) H)
    (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    @Bracket.bracket (GroupLieAlgebra 𝓘(ℂ,V) K)
      (GroupLieAlgebra 𝓘(ℂ,V) K) inferInstance
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) H.subtype 1 u)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) h 1 v) = 0 :=
  complex_bracket_real_derivatives_eq_zero H.subtype h hH hh hComm u v

end
end QuaternionicSymmetry.ComplexLieCentralizerTangent
