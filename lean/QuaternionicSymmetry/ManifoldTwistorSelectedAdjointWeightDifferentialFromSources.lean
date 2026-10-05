import QuaternionicSymmetry.ManifoldTwistorSelectedAdjointCharacterDerivative
import QuaternionicSymmetry.SelectedIntegralCharacterSmooth

/-! The differentiated actual selected-torus adjoint eigenrelation with
literal integral-character smoothness proved from existing general inputs.
The remaining dAd=ad comparison is separate. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedAdjointWeightDifferentialFromSources

open ManifoldTwistorSelectedAdjointCharacterDerivative
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open SelectedIntegralCharacterSmooth
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralDifferentiatedCharacterEigenvector
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem selectedAdjointWeight_mfderiv_from_sources
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
    letI := hTorusChart
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V)
      (fun t : Torus r => selectedAdjointOperator (V := V)
        P n A C hPreserve T t v) 1 w =
    tangentScalarSmul ((weightCharacter μ (1 : Torus r) : Circle) : ℂ) v
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
        (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 w) := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := hTorusChart
  have hχ : MDifferentiableAt 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
      (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 :=
    (weightCharacter_complex_contMDiff μ hTorusChart
      hTorusManifold hTorusLie hClosed hImm hLee).mdifferentiableAt (by simp)
  exact selectedAdjointWeight_mfderiv P n A C hPreserve T μ
    hTorusChart hTorusManifold hχ v hv w

end
end QuaternionicSymmetry.ManifoldTwistorSelectedAdjointWeightDifferentialFromSources
