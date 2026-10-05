import QuaternionicSymmetry.ManifoldTwistorSelectedAdjointBracketDerivative
import QuaternionicSymmetry.ManifoldTwistorSelectedAdjointWeightDifferentialFromSources

/-! An actual selected compact adjoint character differentiates to an
exact Lie-bracket eigenrelation in the SAME transported contact Lie
atlas. No Cartan or root multiplicity hypothesis is used. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedAdjointBracketWeight

open ManifoldTwistorSelectedAdjointBracketDerivative
open ManifoldTwistorSelectedAdjointWeightDifferentialFromSources
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource
open GeneralDifferentiatedCharacterEigenvector
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem selectedAdjointWeight_bracket_generator
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
    (v : V) (hv : v ∈ selectedAdjointWeightSpace (V := V)
      P n A C hPreserve T μ)
    (w : letI := hTorusChart
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
    @Bracket.bracket
      (GroupLieAlgebra 𝓘(ℂ,V)
        (ContactAutomorphisms P.tangent P.connection A C.contact.line))
      (GroupLieAlgebra 𝓘(ℂ,V)
        (ContactAutomorphisms P.tangent P.connection A C.contact.line))
      inferInstance u v =
      tangentScalarSmul ((weightCharacter μ (1 : Torus r) : Circle) : ℂ) v
        (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
          (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 w) := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := hTorusChart
  have hAd := selectedAdjointOperator_mfderiv_eq_bracket_from_sources
    (V := V) hBG9 hR3 hClosed hImm hLee P n A C hPreserve
    T hTorusChart hTorusManifold hTorusLie v w
  have hEig := selectedAdjointWeight_mfderiv_from_sources
    (V := V) hClosed hImm hLee P n A C hPreserve T μ
    hTorusChart hTorusManifold hTorusLie v hv w
  exact hAd.symm.trans hEig

end
end QuaternionicSymmetry.ManifoldTwistorSelectedAdjointBracketWeight
