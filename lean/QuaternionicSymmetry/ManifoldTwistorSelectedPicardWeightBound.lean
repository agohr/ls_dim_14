import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorSelectedPicardReductiveHamiltonian
import QuaternionicSymmetry.ManifoldTwistorSelectedContactToralCartanFromSources
import QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightBoundFromSources

/-! One selected Picard-branch full automorphism atlas and its literal
contact transport jointly carry NT-U Hamiltonian equivariance, central
radical, the actual maximal-isometry-torus Cartan algebra, and the
nonzero-weight multiplicity bound. Only zero centre of THIS contact Lie
algebra remains as a geometric implication premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedPicardWeightBound

open ManifoldTwistorSelectedPicardReductiveHamiltonian
open ManifoldTwistorSelectedContactToralCartanFromSources
open ManifoldTwistorSelectedNonzeroWeightBoundFromSources
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicTorusAction ManifoldQuaternionicSpanSymmetry
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open CompactTorusEigenbasisSource TorusCharacterInput
open GeneralContactFanoPicardUniquenessSource
open GeneralUniqueContactHamiltonianSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource GeneralKillingRadicalSource
open ManifoldTwistorNTContactInfinitesimalSource
open ManifoldTwistorBWW66ReductiveTransformationSource
open ManifoldTwistorFullAutReductiveTransformationTarget
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open ComplexLieToralDifferentialSubalgebra
open scoped Manifold ContDiff
noncomputable section

variable {E M VR : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]

set_option maxHeartbeats 800000 in
theorem exists_selected_picard_cartan_weight_bound
    (hBWW : FullAutReductiveTransformationSource)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hNTU : UniqueContactHamiltonianBijection)
    (hBG9 : LeeRealAdjointDifferentialSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hCompact : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness)
    (hBG : MaximalTorusLieCorrespondenceSource)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hFiniteSections : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hAmple : letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (hPic : letI := A.charts
      letI := A.complexManifold
      Function.Bijective (fun r : ℤ =>
        (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
          (contactClass P.tangent P.connection C.contact.line) :
          SheafClass (B := SphereBundleTotal P.tangent)
            𝓘(ℂ,ComplexTwistorModel n)) ^ r))
    (hRealChart : ChartedSpace VR (QuaternionicIsometries P.tangent))
    (hRealManifold : letI := hRealChart
      IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent))
    (hRealLie : letI := hRealChart
      LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent))
    {r d : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent))
    (g : letI := hRealChart
      EmbeddedRealLieAtlas VR (Torus r) (QuaternionicIsometries P.tangent)
        T.hom d) :
    letI := A.charts
    letI := A.complexManifold
    ∃ (hPreserve : FullPreservesContact
        P.tangent P.connection A C.contact.line)
      (V : Type) (hNorm : NormedAddCommGroup V),
      letI : NormedAddCommGroup V := hNorm
      ∃ (hSpace : NormedSpace ℂ V) (hFinite : FiniteDimensional ℂ V)
        (hChart : ChartedSpace V
          (TwistorHolomorphicAutomorphisms P.tangent P.connection A)),
        letI : NormedSpace ℂ V := hSpace
        letI : FiniteDimensional ℂ V := hFinite
        letI : ChartedSpace V
          (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChart
        ∃ (hManifold : IsManifold 𝓘(ℂ,V) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A))
          (hLie : LieGroup 𝓘(ℂ,V) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A)),
          letI : IsManifold 𝓘(ℂ,V) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifold
          letI : LieGroup 𝓘(ℂ,V) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLie
          ∃ (hJoint : ContMDiff
                (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
                𝓘(ℂ,ComplexTwistorModel n) ∞
                (fun p : TwistorHolomorphicAutomorphisms
                    P.tangent P.connection A × SphereBundleTotal P.tangent =>
                  p.1.1 p.2)),
            letI := contactCharts (V := V)
              P.tangent P.connection A C.contact.line hPreserve
            letI := contactManifold (V := V)
              P.tangent P.connection A C.contact.line hPreserve
            letI := contactLieGroup (V := V)
              P.tangent P.connection A C.contact.line hPreserve
            letI : ENat.LEInfty (minSmoothness ℂ 3) := by
              simpa only [minSmoothness_of_isRCLikeNormedField] using
                (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
            letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
                (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
              LieGroup.of_le (ENat.LEInfty.out)
            let H := toralLieSubalgebra (selectedContactTorusHom P n A C T)
              g.charts g.manifold g.lieGroup
              (selectedContactTorusHom_smooth (V := V)
                hR3 hClosed hImm hLee P n A C hPreserve T
                g.charts g.manifold g.lieGroup)
            LieAlgebra.HasCentralRadical ℂ
              (GroupLieAlgebra 𝓘(ℂ,V)
                (ContactAutomorphisms P.tangent P.connection A C.contact.line)) ∧
            SelectedHamiltonianConjugationLaw (V := V)
              P n A C hPreserve hNTU (by omega) hJoint ∧
            H.IsCartanSubalgebra ∧
            (LieAlgebra.center ℂ (GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line)) = ⊥ →
              ∀ μ : Fin r → ℤ, μ ≠ 0 →
                Module.finrank ℂ (selectedSectionWeightSpace P n A C T μ) ≤ 1) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI : LocallyCompactSpace M := inferInstance
  letI := A.charts
  letI := A.complexManifold
  obtain ⟨hPreserve,V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hJoint,hRad,hConj⟩ :=
    exists_selected_picard_reductive_hamiltonian hBWW hUnique hNTU
      P n hn hDim A C hAmple hPic
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLie
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  letI : ChartedSpace VR (QuaternionicIsometries P.tangent) := hRealChart
  letI : IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealManifold
  letI : LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealLie
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : ENat.LEInfty (minSmoothness ℂ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    LieGroup.of_le (ENat.LEInfty.out)
  have hCartan := selectedContactToralLie_isCartan_from_sources
    hNT hNTU hBG9 hR3 hCompact hBG hClosed hImm hLee
    hFiniteSections hEigen hCircle P n hn hDim A C hPreserve
    hRealChart hRealManifold hRealLie hJoint T hMax g
  refine ⟨hPreserve,V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,
    hJoint,hRad,hConj,hCartan,?_⟩
  intro hCenter μ hμ
  exact selected_nonzero_section_weight_finrank_le_one_from_sources
    hNT hNTU hBG9 hR3 hCompact hBG hClosed hImm hLee
    hFiniteSections hEigen hCircle P n hn hDim A C hPreserve
    hRealChart hRealManifold hRealLie hJoint T hMax g hRad hCenter μ hμ

end
end QuaternionicSymmetry.ManifoldTwistorSelectedPicardWeightBound
