import QuaternionicSymmetry.ManifoldTwistorSelectedToralBracketEigenbasis
import QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianEigenbasis

/-! The actual integral contact-section eigenbasis, transported by the
canonical Hamiltonian equivalence in the SAME selected complex contact Lie
atlas, is a common bracket eigenbasis for the selected toral subalgebra. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianToralBracketBasis

open ManifoldTwistorSelectedHamiltonianEigenbasis
open ManifoldTwistorSelectedToralBracketEigenbasis
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorUniqueContactHamiltonianEquivarianceFromSources
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs CompactTorusEigenbasisSource TorusCharacterInput
open GeneralUniqueContactHamiltonianSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource
open ComplexLieToralDifferentialSubalgebra
open HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
  [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem exists_selectedHamiltonian_toral_bracket_eigenbasis
    (hNTU : UniqueContactHamiltonianBijection)
    (hBG9 : LeeRealAdjointDifferentialSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hAutChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hJoint :
      letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2))
    {r d : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (hTorusChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hTorusManifold : letI := hTorusChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hTorusLie : letI := hTorusChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r)) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := hTorusChart
    letI := hTorusManifold
    letI := hTorusLie
    let ρ := selectedContactTorusHom P n A C T
    let hSmooth := selectedContactTorusHom_smooth (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      hTorusChart hTorusManifold hTorusLie
    let H := toralLieSubalgebra ρ hTorusChart hTorusManifold hTorusLie hSmooth
    ∃ bL : Module.Basis
      (Fin (Module.finrank ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line)))) ℂ V,
      ∃ μ : Fin (Module.finrank ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))) → Fin r → ℤ,
      ∃ χ : H → Fin (Module.finrank ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))) → ℂ,
        (∀ i, bL i ∈ selectedAdjointWeightSpace (V := V)
          P n A C hPreserve T (μ i)) ∧
        ∀ (h : H) i,
          @Bracket.bracket
            (GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line))
            (GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line))
            inferInstance
            (h : GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line))
            (bL i : GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line)) =
            χ h i • (bL i : GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line)) := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := hTorusChart
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hTorusManifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hTorusLie
  obtain ⟨bS, μ, hEig, hLaurent, hMem, hPre⟩ :=
    exists_selectedHamiltonian_eigenbasis_from_sources (V := V)
      hNTU hR3 hFinite hEigen hCircle P n hn A C hPreserve hJoint T
  let F := canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
    hNTU P n hn A C hPreserve hJoint
  let bL : Module.Basis _ ℂ V := bS.map F.symm
  have hImage (i) : F (bL i) = bS i := by
    change F (F.symm (bS i)) = bS i
    exact F.apply_symm_apply _
  have hWeight (i) : bL i ∈ selectedAdjointWeightSpace (V := V)
      P n A C hPreserve T (μ i) := by
    obtain ⟨v, hv, hFv, _⟩ := hPre i
    have hvEq : v = bL i := F.injective (hFv.trans (hImage i).symm)
    rw [← hvEq]
    exact hv
  obtain ⟨χ, hχ⟩ := exists_selected_toral_bracket_eigenbasis (V := V)
    hBG9 hR3 hClosed hImm hLee P n A C hPreserve T
    hTorusChart hTorusManifold hTorusLie bL μ hWeight
  exact ⟨bL, μ, χ, hWeight, hχ⟩

end
end QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianToralBracketBasis
