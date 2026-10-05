import QuaternionicSymmetry.SelectedIntegralCharacterDerivativeFromExp
import QuaternionicSymmetry.SelectedTorusCompactExponentialLift

/-! Fully source-only nonvanishing of a nonzero integral character's
identity differential in the SAME selected BG-L3 embedded-torus atlas.
No character-rigidity literature premise is added. -/

namespace QuaternionicSymmetry.SelectedIntegralCharacterDerivativeFromEmbeddedAtlas

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusCompactExponentialLift
open SelectedIntegralCharacterDerivativeFromExp
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r d : ℕ}

theorem weightCharacter_mfderiv_ne_zero_selected
    (T : TorusEmbedding G r)
    (g : EmbeddedRealLieAtlas V (Torus r) G T.hom d)
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI := g.charts
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
      (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 ≠ 0 := by
  exact weightCharacter_mfderiv_ne_zero_of_exp
    μ hμ g.charts g.manifold g.lieGroup hClosed hImm hLee
    (circleExpPi_smooth_selected T g hClosed hImm hLee)

end
end QuaternionicSymmetry.SelectedIntegralCharacterDerivativeFromEmbeddedAtlas
