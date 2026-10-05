import QuaternionicSymmetry.ManifoldTwistorSelectedAdjointWeightRootInclusion
import QuaternionicSymmetry.ToralBracketEigenbasis

/-! Integral adjoint eigenvectors form a bracket eigenbasis for the actual
selected toral Lie subalgebra, in the SAME transported complex contact atlas.
The toral subalgebra need not yet be Cartan. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedToralBracketEigenbasis

open ManifoldTwistorSelectedAdjointBracketWeight
open ManifoldTwistorSelectedContactTorusSmooth
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
open ComplexLieToralDifferentialSubalgebra
open ToralBracketEigenbasis
open scoped Manifold ContDiff
noncomputable section

variable {E M V ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

/-- A genuine basis whose vectors lie in the selected integral adjoint
weight spaces is a bracket eigenbasis for the differential-generated H.
All brackets are in the full-Aut-transported contact Lie atlas. -/
theorem exists_selected_toral_bracket_eigenbasis
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
    (b : Module.Basis ι ℂ V) (μ : ι → Fin r → ℤ)
    (hWeight : ∀ i, b i ∈ selectedAdjointWeightSpace (V := V)
      P n A C hPreserve T (μ i)) :
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
    let bL : Module.Basis ι ℂ (GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) := b
    ∃ χ : H → ι → ℂ, ∀ (h : H) i,
      ⁅(h : GroupLieAlgebra 𝓘(ℂ,V)
        (ContactAutomorphisms P.tangent P.connection A C.contact.line)), bL i⁆ =
        χ h i • bL i := by
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
  let bL : Module.Basis ι ℂ (GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) := b
  let S : Set (GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) :=
    differentialGenerators (V := V) ρ hTorusChart
  have hComm : ∀ x ∈ S, ∀ y ∈ S, ⁅x,y⁆ = 0 := by
    intro x hx y hy
    exact differentialGenerators_bracket_zero (V := V) ρ hTorusChart
      hTorusManifold hTorusLie hSmooth hx hy
  have hEigGen : ∀ i, ∀ s ∈ S, ∃ c : ℂ, ⁅s,bL i⁆ = c • bL i := by
    intro i s hs
    obtain ⟨w, rfl⟩ := hs
    let c : ℂ := mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
      (fun t : Torus r => (weightCharacter (μ i) t : ℂ)) 1 w
    refine ⟨c, ?_⟩
    have h := selectedAdjointWeight_bracket_generator (V := V)
      hBG9 hR3 hClosed hImm hLee P n A C hPreserve T (μ i)
      hTorusChart hTorusManifold hTorusLie (b i) (hWeight i) w
    have htransport {a c : ContactAutomorphisms
        P.tangent P.connection A C.contact.line} (hac : a = c)
        (u : TangentSpace 𝓘(ℝ,V) a) :
        (hac ▸ u : TangentSpace 𝓘(ℝ,V) c) = (u : V) := by
      cases hac
      rfl
    have h0 :
        (ρ.map_one ▸ mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w :
          TangentSpace 𝓘(ℝ,V)
            (1 : ContactAutomorphisms P.tangent P.connection A C.contact.line)) =
          (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w : V) :=
      htransport ρ.map_one _
    let Lc := GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)
    let br : Lc → Lc := fun x => @Bracket.bracket Lc Lc inferInstance x (bL i)
    have hbr := congrArg br h0.symm
    have hscalar : tangentScalarSmul (V := V)
        ((weightCharacter (μ i) (1 : Torus r) : Circle) : ℂ) (b i : V)
        (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
          (fun t : Torus r => (weightCharacter (μ i) t : ℂ)) 1 w) =
        c • bL i := by
      change c • (b i : V) = c • bL i
      rfl
    exact hbr.trans (h.trans hscalar)
  exact exists_bracket_eigenbasis S hComm bL hEigGen

end
end QuaternionicSymmetry.ManifoldTwistorSelectedToralBracketEigenbasis
