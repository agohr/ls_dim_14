import QuaternionicSymmetry.ManifoldTwistorSelectedAdjointBracketWeight
import QuaternionicSymmetry.ManifoldTwistorSelectedContactToralLieFromSources
import QuaternionicSymmetry.ToralCommonWeightRootInclusion
import QuaternionicSymmetry.ComplexLieToralRootSpace

/-! The entire nonzero selected compact adjoint weight space lies in ONE
generalized root space of the actual selected complex toral Lie
subalgebra. The root character is constructed from an anchor vector,
not assumed to descend along the torus differential. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedAdjointWeightRootInclusion

open ManifoldTwistorSelectedAdjointBracketWeight
open ManifoldTwistorSelectedContactToralLieFromSources
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ComplexLieToralDifferentialSubalgebra
open ToralCommonWeightRootInclusion
open GeneralDifferentiatedCharacterEigenvector
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

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem exists_selected_weight_root_inclusion
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
    {r d : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (μ : Fin r → ℤ)
    (hTorusChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hTorusManifold : letI := hTorusChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hTorusLie : letI := hTorusChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
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
    letI := hTorusChart
    letI := hTorusManifold
    letI := hTorusLie
    let ρ := selectedContactTorusHom P n A C T
    let hSmooth := selectedContactTorusHom_smooth (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      hTorusChart hTorusManifold hTorusLie
    let H := toralLieSubalgebra ρ hTorusChart hTorusManifold hTorusLie hSmooth
    letI := ComplexLieToralRootSpace.toralLie_isNilpotent
      ρ hTorusChart hTorusManifold hTorusLie hSmooth
    ∃ α : H → ℂ,
      selectedAdjointWeightSpace (V := V) P n A C hPreserve T μ ≤
        (LieAlgebra.rootSpace H α).toSubmodule := by
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
  let ρ := selectedContactTorusHom P n A C T
  let hSmooth := selectedContactTorusHom_smooth (V := V)
    hR3 hClosed hImm hLee P n A C hPreserve T
    hTorusChart hTorusManifold hTorusLie
  let S : Set (GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) :=
    differentialGenerators (V := V) ρ hTorusChart
  let H := toralLieSubalgebra (V := V) ρ hTorusChart hTorusManifold hTorusLie hSmooth
  let W : Submodule ℂ (GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) :=
    selectedAdjointWeightSpace (V := V) P n A C hPreserve T μ
  obtain ⟨v₀, hv₀, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hComm : ∀ x ∈ S, ∀ y ∈ S, ⁅x,y⁆ = 0 := by
    intro x hx y hy
    exact differentialGenerators_bracket_zero (V := V) ρ hTorusChart
      hTorusManifold hTorusLie hSmooth hx hy
  have hEig : ∀ s ∈ S, ∃ c : ℂ, ∀ v ∈ W, ⁅s,v⁆ = c • v := by
    intro s hs
    obtain ⟨w, rfl⟩ := hs
    refine ⟨mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
      (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 w, ?_⟩
    intro v hv
    have h := selectedAdjointWeight_bracket_generator (V := V)
      hBG9 hR3 hClosed hImm hLee P n A C hPreserve T μ
      hTorusChart hTorusManifold hTorusLie v hv w
    have htransport {a b : ContactAutomorphisms
        P.tangent P.connection A C.contact.line} (hab : a = b)
        (u : TangentSpace 𝓘(ℝ,V) a) :
        (hab ▸ u : TangentSpace 𝓘(ℝ,V) b) = (u : V) := by
      cases hab
      rfl
    have h0 :
        (ρ.map_one ▸ mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w :
          TangentSpace 𝓘(ℝ,V)
            (1 : ContactAutomorphisms P.tangent P.connection A C.contact.line)) =
          (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w : V) :=
      htransport ρ.map_one _
    let Lc := GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)
    let br : Lc → Lc := fun x => @Bracket.bracket Lc Lc inferInstance x v
    have hbr := congrArg br h0.symm
    have hscalar : tangentScalarSmul (V := V)
        ((weightCharacter μ (1 : Torus r) : Circle) : ℂ) (v : V)
        (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
          (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 w) =
        (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
          (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 w) • (v : V) := rfl
    exact hbr.trans (h.trans hscalar)
  letI := ComplexLieToralRootSpace.toralLie_isNilpotent (V := V)
    ρ hTorusChart hTorusManifold hTorusLie hSmooth
  exact ⟨anchorCharacter S hComm W hEig v₀ hv₀,
    submodule_le_rootSpace S hComm W hEig v₀ hv₀ hv₀ne⟩

end
end QuaternionicSymmetry.ManifoldTwistorSelectedAdjointWeightRootInclusion
