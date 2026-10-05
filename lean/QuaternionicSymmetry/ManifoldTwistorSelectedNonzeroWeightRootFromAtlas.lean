import QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightRoot
import QuaternionicSymmetry.SelectedTorusCompactExponentialLift

/-! The same selected BG-L3 embedded real atlas supplies the coordinate
exponential smoothness required for the actual nonzero-root theorem.
The contact Lie atlas remains exactly the transported supplied atlas. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightRootFromAtlas

open ManifoldTwistorSelectedNonzeroWeightRoot
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ComplexLieToralDifferentialSubalgebra ComplexLieToralRootSpace
open SelectedTorusCompactExponentialLift
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource
open scoped Manifold ContDiff
noncomputable section

variable {E M V VR : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem exists_selected_nonzero_weight_root_inclusion_from_atlas
    (hBG9 : LeeRealAdjointDifferentialSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hAutChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hQChart : ChartedSpace VR
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)]
    [hQManifold : IsManifold 𝓘(ℝ,VR) ∞
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)]
    [hQLie : LieGroup 𝓘(ℝ,VR) ∞
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)]
    [hQT2 : T2Space
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)]
    [hQSecond : SecondCountableTopology
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)]
    {r d : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (g : EmbeddedRealLieAtlas VR (Torus r)
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) T.hom d)
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hW : selectedAdjointWeightSpace (V := V)
      P n A C hPreserve T μ ≠ ⊥) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := g.charts
    letI := g.manifold
    letI := g.lieGroup
    let ρ := selectedContactTorusHom P n A C T
    let hSmooth := selectedContactTorusHom_smooth (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup
    let H := toralLieSubalgebra ρ g.charts g.manifold g.lieGroup hSmooth
    letI := toralLie_isNilpotent ρ g.charts g.manifold g.lieGroup hSmooth
    ∃ α : H → ℂ, α ≠ 0 ∧
      selectedAdjointWeightSpace (V := V) P n A C hPreserve T μ ≤
        (LieAlgebra.rootSpace H α).toSubmodule := by
  exact exists_selected_nonzero_weight_root_inclusion_of_exp (V := V)
    hBG9 hR3 hClosed hImm hLee P n A C hPreserve T μ hμ
    g.charts g.manifold g.lieGroup
    (circleExpPi_smooth_selected T g hClosed hImm hLee) hW

end
end QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightRootFromAtlas
