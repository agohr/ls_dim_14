import QuaternionicSymmetry.GeneralDifferentiatedCharacterEigenvector
import QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianWeightSpaces

/-! Differentiation of the selected *actual* compact-torus adjoint
eigenrelation. This gives an equality of genuine manifold derivatives.
Identifying the adjoint-orbit derivative with the Lie bracket, and the
character derivative with an integral root functional, are separate gates. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedAdjointCharacterDerivative

open GeneralDifferentiatedCharacterEigenvector
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem selectedAdjointWeight_mfderiv
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
    (hχ : letI := hTorusChart
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ,ℂ)
        (fun t : Torus r => (weightCharacter μ t : ℂ)) 1)
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
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hTorusManifold
  exact mfderiv_eigenvector_of_character
    (selectedAdjointOperator (V := V) P n A C hPreserve T)
    (fun t : Torus r => (weightCharacter μ t : ℂ)) v 1 hv hχ w

end
end QuaternionicSymmetry.ManifoldTwistorSelectedAdjointCharacterDerivative
