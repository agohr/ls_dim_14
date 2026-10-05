import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ComplexToralDifferentialSelfCentralizing
import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusFullLieCentralizer
import QuaternionicSymmetry.SelectedTorusLieSpanDerivativeEquality
import QuaternionicSymmetry.ManifoldTwistorSelectedContactToralLieSubalgebra
import QuaternionicSymmetry.SmoothLieHomDerivativeBracket
import QuaternionicSymmetry.ComplexGroupLieBracketRestriction

/-! Same-atlas actual selected contact toral self-centralizer. The only
geometric input is the BG-L1 maximal-torus correspondence. The separately
proved real/complex differential comparison is supplied explicitly here;
NT-C discharges it in the subsequent source-only application. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedContactToralSelfCentralizing

open ComplexToralDifferentialSelfCentralizing
open ManifoldQuaternionicMaximalTorusFullLieCentralizer
open SelectedTorusLieSpanDerivativeEquality SelectedTorusEmbeddedLieAtlas
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicTorusAction ManifoldQuaternionicSpanSymmetry
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open RealToComplexTangentComplexification ComplexLieRealCompanion
open SmoothLieHomDerivativeBracket
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]

theorem selectedContactToralLie_selfCentralizing
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hCompact : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness)
    (hBG : MaximalTorusLieCorrespondenceSource)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
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
    {r d : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent))
    (g : letI := hRealChart
      EmbeddedRealLieAtlas VR (Torus r) (QuaternionicIsometries P.tangent)
        T.hom d)
    (hSmoothLift : letI := A.charts
      letI := A.complexManifold
      letI := hRealChart
      letI := contactCharts (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      ContMDiff 𝓘(ℝ,VR) 𝓘(ℝ,VC) ∞
        (isometryContactLift P.tangent P.connection A C.contact.line))
    (hSmoothρ : letI := A.charts
      letI := A.complexManifold
      letI := contactCharts (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      letI := g.charts
      ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC) ∞
        (selectedContactTorusHom P n A C T))
    (hBij : letI := A.charts
      letI := A.complexManifold
      letI := hRealChart
      letI := contactCharts (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      Function.Bijective (complexifiedMapComplex
        (show GroupLieAlgebra 𝓘(ℝ,VR) (QuaternionicIsometries P.tangent)
          →ₗ[ℝ] GroupLieAlgebra 𝓘(ℂ,VC)
            (ContactAutomorphisms P.tangent P.connection A C.contact.line) from
          (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC)
            (isometryContactLift P.tangent P.connection A C.contact.line) 1).toLinearMap))) :
    letI := A.charts
    letI := A.complexManifold
    letI := hRealChart
    letI := hRealManifold
    letI := hRealLie
    letI := contactCharts (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    let H := selectedContactToralLieSubalgebra
      P n A C hPreserve T g.charts g.manifold g.lieGroup hSmoothρ
    ∀ z : GroupLieAlgebra 𝓘(ℂ,VC)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line),
      z ∈ H ↔ ∀ w ∈ H, ⁅z,w⁆ = 0 := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI : ChartedSpace VR (QuaternionicIsometries P.tangent) := hRealChart
  letI : IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealManifold
  letI : LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealLie
  letI : CompactSpace (QuaternionicIsometries P.tangent) := by
    exact hCompact
      P.toPositiveQuaternionicKahlerGeometry n hn hDim
  letI : SecondCountableTopology (QuaternionicIsometries P.tangent) :=
    ChartedSpace.secondCountable_of_sigmaCompact VR _
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI : IsManifold 𝓘(ℝ,VC) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := realManifold
  letI : LieGroup 𝓘(ℝ,VC) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := realLieGroup
  letI : CompleteSpace VR := FiniteDimensional.complete ℝ VR
  letI : CompleteSpace VC := FiniteDimensional.complete ℂ VC
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  letI : ENat.LEInfty (minSmoothness ℂ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.lieGroup
  obtain ⟨hAb,hSelf⟩ := selected_torus_full_lie_selfCentralizing
    P.toPositiveQuaternionicKahlerGeometry n hn hDim hCompact
    hRealChart hRealLie hBG T hMax
  have hRange := torusLieSpan_eq_derivative_range T g hImm hLee
  exact fun z => by
    have hBracket (x y : GroupLieAlgebra 𝓘(ℝ,VR)
        (QuaternionicIsometries P.tangent)) :
        (show GroupLieAlgebra 𝓘(ℂ,VC)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line) from
          mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC)
            (isometryContactLift P.tangent P.connection A C.contact.line) 1 ⁅x,y⁆) =
          ⁅(show GroupLieAlgebra 𝓘(ℂ,VC)
            (ContactAutomorphisms P.tangent P.connection A C.contact.line) from
            mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC)
              (isometryContactLift P.tangent P.connection A C.contact.line) 1 x),
            (show GroupLieAlgebra 𝓘(ℂ,VC)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line) from
              mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC)
                (isometryContactLift P.tangent P.connection A C.contact.line) 1 y)⁆ :=
      (mfderiv_map_lie _ hSmoothLift x y).trans
        (ComplexGroupLieBracketRestriction.bracket_real_eq_complex (V := VC)
          (K := ContactAutomorphisms P.tangent P.connection A C.contact.line)
          _ _)
    exact differential_span_selfCentralizing T g.charts
      (selected_hom_smooth T g)
      (isometryContactLift P.tangent P.connection A C.contact.line)
      hSmoothLift hRange hAb hSelf hBij hBracket z

end
end QuaternionicSymmetry.ManifoldTwistorSelectedContactToralSelfCentralizing
