import QuaternionicSymmetry.CompactRealFormKilling
import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightRootBound
import QuaternionicSymmetry.ManifoldTwistorSelectedContactToralCartanFromSources

/-! Source-only actual nonzero integral weight multiplicity bound, except
for the two clearly exposed SAME-atlas Lie conditions: central radical and
zero centre. The selected Cartan condition is proved internally from the
actual torus and Hamiltonian representation, not supplied as an input. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightBoundFromSources

open ManifoldTwistorSelectedNonzeroWeightRootBound
open ManifoldTwistorSelectedContactToralCartanFromSources
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicTorusAction ManifoldQuaternionicSpanSymmetry
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open CompactTorusEigenbasisSource TorusCharacterInput
open GeneralUniqueContactHamiltonianSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource GeneralKillingRadicalSource
open ManifoldTwistorNTContactInfinitesimalSource
open scoped Manifold ContDiff
noncomputable section

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

set_option maxHeartbeats 800000 in
theorem selected_nonzero_section_weight_finrank_le_one_from_sources
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
        T.hom d)
    (hRad : letI := A.charts
      letI := A.complexManifold
      letI := contactCharts (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      letI := contactLieGroup (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      letI : LieGroup 𝓘(ℂ,VC) (minSmoothness ℂ 3)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
        LieGroup.of_le (ENat.LEInfty.out)
      LieAlgebra.HasCentralRadical ℂ
        (GroupLieAlgebra 𝓘(ℂ,VC)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line)))
    (hCenter : letI := A.charts
      letI := A.complexManifold
      letI := contactCharts (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      letI := contactLieGroup (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      LieAlgebra.center ℂ (GroupLieAlgebra 𝓘(ℂ,VC)
        (ContactAutomorphisms P.tangent P.connection A C.contact.line)) = ⊥)
    (μ : Fin r → ℤ) (hμ : μ ≠ 0) :
    Module.finrank ℂ (selectedSectionWeightSpace P n A C T μ) ≤ 1 := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI : LocallyCompactSpace M := inferInstance
  letI : ChartedSpace VR (QuaternionicIsometries P.tangent) := hRealChart
  letI : IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealManifold
  letI : LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealLie
  letI : CompactSpace (QuaternionicIsometries P.tangent) := by
    exact hCompact
      P.toPositiveQuaternionicKahlerGeometry n hn hDim
  letI : SecondCountableTopology (QuaternionicIsometries P.tangent) :=
    ChartedSpace.secondCountable_of_sigmaCompact VR _
  have hCartan := selectedContactToralLie_isCartan_from_sources
    hNT hNTU hBG9 hR3 hCompact hBG hClosed hImm hLee
    hFinite hEigen hCircle P n hn hDim A C hPreserve
    hRealChart hRealManifold hRealLie hJoint T hMax g
  have hBij := ManifoldTwistorNTContactInfinitesimalApplication.actual_contact_lift_complexified_bijective
    hNT hR3 hCompact hClosed hImm hLee P n hn hDim A C hPreserve
    hRealChart hRealManifold hRealLie hJoint
  have hSmooth := ManifoldTwistorContactLiftSmoothFromSources.actual_contact_lift_smooth (VC := VC)
    hR3 hCompact hClosed hImm hLee P n hn hDim A C hPreserve
    hRealChart hRealManifold hRealLie
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := VC) P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := VC) P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := VC) P.tangent P.connection A C.contact.line hPreserve
  letI : SecondCountableTopology
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := by
    change SecondCountableTopology
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (ManifoldTwistorContactAutomorphisms.contactDistribution P.tangent P.connection A C.contact.line))
    infer_instance
  have hKilling := CompactRealFormKilling.isKilling_of_compact_complexification
    (isometryContactLift P.tangent P.connection A C.contact.line) hSmooth hBij.2 hCenter
  exact selected_nonzero_weight_finrank_le_one_of_cartan_center
    hBG9 hR3 hClosed hImm hLee hNTU
    P n (by omega : 1 ≤ n) A C hPreserve hJoint
    T g hCartan hKilling hCenter μ hμ

end
end QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightBoundFromSources
