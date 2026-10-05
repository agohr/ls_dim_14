import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorSelectedContactToralSelfCentralizingFromSources
import QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianToralBracketBasis
import QuaternionicSymmetry.AbelianSelfCentralizingEigenbasisCartan

/-! The SAME selected maximal isometry torus generates a genuine Cartan
subalgebra of the selected contact automorphism Lie algebra. Self-
centralization comes from BG-L1 plus NT-C; the common bracket eigenbasis
comes from the actual contact Hamiltonian section representation. This
is a kernel-checked internal combination, not a Cartan source premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedContactToralCartanFromSources

open ManifoldTwistorSelectedContactToralSelfCentralizingFromSources
open ManifoldTwistorSelectedHamiltonianToralBracketBasis
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open CompactTorusEigenbasisSource TorusCharacterInput
open GeneralUniqueContactHamiltonianSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource
open ManifoldTwistorNTContactInfinitesimalSource
open ComplexLieToralDifferentialSubalgebra
open AbelianSelfCentralizingEigenbasisCartan
open scoped Manifold ContDiff
noncomputable section

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
  [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

set_option maxHeartbeats 800000 in
theorem selectedContactToralLie_isCartan_from_sources
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hNTU : UniqueContactHamiltonianBijection)
    (hBG9 : LeeRealAdjointDifferentialSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hCompact : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness)
    (hBG : MaximalTorusLieCorrespondenceSource)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    (hRealChart : ChartedSpace VR (QuaternionicIsometries P.tangent))
    (hRealManifold : letI := hRealChart
      IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent))
    (hRealLie : letI := hRealChart
      LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent))
    [hAutChart : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutManifold : IsManifold 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutLie : LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hJoint : letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,VC).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms
            P.tangent P.connection A × SphereBundleTotal P.tangent => p.1.1 p.2))
    {r d : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent))
    (g : letI := hRealChart
      EmbeddedRealLieAtlas VR (Torus r) (QuaternionicIsometries P.tangent)
        T.hom d) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    let H := toralLieSubalgebra (selectedContactTorusHom P n A C T)
      g.charts g.manifold g.lieGroup
      (selectedContactTorusHom_smooth (V := VC)
        hR3 hClosed hImm hLee P n A C hPreserve T
        g.charts g.manifold g.lieGroup)
    H.IsCartanSubalgebra := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.lieGroup
  let H := toralLieSubalgebra (selectedContactTorusHom P n A C T)
    g.charts g.manifold g.lieGroup
    (selectedContactTorusHom_smooth (V := VC)
      hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup)
  have hSelf : ∀ z : GroupLieAlgebra 𝓘(ℂ,VC)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line),
      z ∈ H ↔ ∀ w ∈ H, ⁅z,w⁆ = 0 :=
    selectedContactToralLie_selfCentralizing_from_sources
      hNT hR3 hCompact hBG hClosed hImm hLee
      P n hn hDim A C hPreserve hRealChart hRealManifold hRealLie
      hJoint T hMax g
  obtain ⟨bL, μ, χ, hWeight, hEig⟩ :=
    exists_selectedHamiltonian_toral_bracket_eigenbasis (V := VC)
      hNTU hBG9 hR3 hClosed hImm hLee hFinite hEigen hCircle
      P n (by omega : 1 ≤ n) A C hPreserve hJoint T
      g.charts g.manifold g.lieGroup
  exact isCartan_of_abelian_selfCentralizing_eigenbasis H
    (fun x hx y hy => toralLieSubalgebra_abelian
      (selectedContactTorusHom P n A C T) g.charts g.manifold g.lieGroup
      (selectedContactTorusHom_smooth (V := VC)
        hR3 hClosed hImm hLee P n A C hPreserve T
        g.charts g.manifold g.lieGroup) ⟨x,hx⟩ ⟨y,hy⟩)
    (fun z hz => (hSelf z).2 hz) bL χ hEig

end
end QuaternionicSymmetry.ManifoldTwistorSelectedContactToralCartanFromSources
