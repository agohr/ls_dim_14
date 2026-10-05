import QuaternionicSymmetry.GeneralComplexAdjointTorusChain
import QuaternionicSymmetry.GeneralComplexAdjointFromReal
import QuaternionicSymmetry.ManifoldTwistorSelectedContactTorusSmooth
import QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianWeightSpaces

/-! The selected actual quaternionic-isometry torus, lifted to contact
automorphisms, has the genuine complex Lie-algebra adjoint derivative in
the SAME atlas as the selected canonical Hamiltonian equivalence. This is
an internal specialization of general real BG-L9 and the checked torus
chain, not a model-specific Lie-root input. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedAdjointBracketDerivative

open GeneralComplexAdjointTorusChain GeneralComplexAdjointFromReal
open GeneralRealAdjointDifferentialSource
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open GeneralHolomorphicAutomorphismSecondCountable
open CompactLieTorusInputs
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The literal selected adjoint-operator derivative is the bracket with
the actual derivative of the selected compact torus lift. The result uses
exactly the transported contact atlas from the supplied full-Aut atlas. -/
theorem selectedAdjointOperator_mfderiv_eq_bracket
    (hBG9 : LeeRealAdjointDifferentialSource)
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
    (hTorusChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hTorusManifold : letI := hTorusChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hTorusLie : letI := hTorusChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hSmooth :
      letI := A.charts
      letI := A.complexManifold
      letI := contactCharts (V := V)
        P.tangent P.connection A C.contact.line hPreserve
      letI := hTorusChart
      ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ∞
        (selectedContactTorusHom P n A C T))
    (v : V) (w : letI := hTorusChart
      TangentSpace 𝓘(ℝ,Fin d → ℝ) (1 : Torus r)) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := hTorusChart
    let ρ := selectedContactTorusHom P n A C T
    let u : TangentSpace 𝓘(ℝ,V)
        (1 : ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
      ρ.map_one ▸ mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V)
        (fun t : Torus r => selectedAdjointOperator (V := V)
          P n A C hPreserve T t v) 1 w =
      @Bracket.bracket
        (GroupLieAlgebra 𝓘(ℂ,V)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line))
        (GroupLieAlgebra 𝓘(ℂ,V)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line))
        inferInstance u v := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : LocallyCompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal P.tangent) := inferInstance
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : SecondCountableTopology
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := by
    change SecondCountableTopology
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (contactDistribution P.tangent P.connection A C.contact.line))
    infer_instance
  letI := hTorusChart
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hTorusManifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hTorusLie
  let ρ := selectedContactTorusHom P n A C T
  have hChain := mfderiv_adjointOrbit_comp_lieHom
    (V := V) (F := Fin d → ℝ)
    (T := Torus r)
    (G := ContactAutomorphisms P.tangent P.connection A C.contact.line)
    (complexAdjointDifferential_of_real hBG9) ρ hSmooth v w
  exact hChain

/-- Source-only version: actual compact isometry Lie input and the
registered general Lee smooth-hom inputs prove the selected torus lift is
smooth; no smoothness of its adjoint orbit is supplied separately. -/
theorem selectedAdjointOperator_mfderiv_eq_bracket_from_sources
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
    (hTorusChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hTorusManifold : letI := hTorusChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hTorusLie : letI := hTorusChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (v : V) (w : letI := hTorusChart
      TangentSpace 𝓘(ℝ,Fin d → ℝ) (1 : Torus r)) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := hTorusChart
    let ρ := selectedContactTorusHom P n A C T
    let u : TangentSpace 𝓘(ℝ,V)
        (1 : ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
      ρ.map_one ▸ mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V)
        (fun t : Torus r => selectedAdjointOperator (V := V)
          P n A C hPreserve T t v) 1 w =
      @Bracket.bracket
        (GroupLieAlgebra 𝓘(ℂ,V)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line))
        (GroupLieAlgebra 𝓘(ℂ,V)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line))
        inferInstance u v := by
  exact selectedAdjointOperator_mfderiv_eq_bracket (V := V)
    hBG9 P n A C hPreserve T hTorusChart hTorusManifold hTorusLie
    (selectedContactTorusHom_smooth (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      hTorusChart hTorusManifold hTorusLie) v w

end
end QuaternionicSymmetry.ManifoldTwistorSelectedAdjointBracketDerivative
