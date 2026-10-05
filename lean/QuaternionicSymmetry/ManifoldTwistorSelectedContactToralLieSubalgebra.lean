import QuaternionicSymmetry.ComplexLieToralDifferentialSubalgebra
import QuaternionicSymmetry.ManifoldTwistorUniqueContactHamiltonianEquivarianceFromSources

/-! The selected isometry torus yields an actual abelian complex Lie
subalgebra of the SAME transported contact-automorphism atlas, given its
real-smooth group homomorphism. No Cartan/maximality assertion is made. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedContactToralLieSubalgebra

open ComplexLieToralDifferentialSubalgebra
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

def selectedContactTorusHom
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    {r : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r) :
    Torus r →* ContactAutomorphisms P.tangent P.connection A C.contact.line :=
  (isometryContactLift P.tangent P.connection A C.contact.line).comp T.hom

/-- The selected actual contact torus generates an abelian Lie subalgebra
in the SAME contact Lie algebra model used by the Hamiltonian equivalence. -/
def selectedContactToralLieSubalgebra
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
    (hSmooth : letI := A.charts
      letI := A.complexManifold
      letI := contactCharts (V := V)
        P.tangent P.connection A C.contact.line hPreserve
      letI := hTorusChart
      ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ∞
        (selectedContactTorusHom P n A C T)) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    LieSubalgebra ℂ (GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  exact toralLieSubalgebra (selectedContactTorusHom P n A C T)
    hTorusChart hTorusManifold hTorusLie hSmooth

end
end QuaternionicSymmetry.ManifoldTwistorSelectedContactToralLieSubalgebra
