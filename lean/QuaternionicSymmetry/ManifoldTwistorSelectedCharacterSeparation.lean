import QuaternionicSymmetry.SelectedTorusSpanningCharacterImage
import QuaternionicSymmetry.ManifoldTwistorSelectedTorusComplexifiedRange
import QuaternionicSymmetry.ManifoldTwistorSelectedComplexifiedCharactersFromSources

/-! Conditional character separation on the genuine selected toral Lie
subalgebra H of the actual twistor contact automorphism group. The SAME
BG-L3 embedded torus atlas is used for both the coordinate derivative and
the selected compact-to-contact infinitesimal map. Real spanning of these
particular integral weights remains an explicit geometric hypothesis. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedCharacterSeparation

open SelectedTorusSpanningCharacterImage
open IntegralWeightRealSpanComplexSeparation
open ManifoldTwistorSelectedTorusComplexifiedRange
open ManifoldTwistorSelectedTorusComplexifiedDifferential
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ComplexLieToralDifferentialSubalgebra
open RealToComplexTangentComplexification
open TorusWeightCharacterDifferentialLinear
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M V VR : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem selected_toral_characters_separate_of_real_span
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
    [hQChart : ChartedSpace VR
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)]
    [hQManifold : IsManifold 𝓘(ℝ,VR) ∞
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)]
    [hQLie : LieGroup 𝓘(ℝ,VR) ∞
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)]
    [hQT2 : T2Space
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)]
    [hQSecond : SecondCountableTopology
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)]
    {r d : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (g : EmbeddedRealLieAtlas VR (Torus r)
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) T.hom d)
    {ι : Type*} (μ : ι → Fin r → ℤ)
    (hSpan : Submodule.span ℝ
      (Set.range (fun i => realWeightVector (μ i))) = ⊤) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := g.charts
    letI := g.manifold
    letI := g.lieGroup
    let f := selectedTorusDifferentialIntoH (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup
    let ρ := selectedContactTorusHom P n A C T
    let hSmooth := selectedContactTorusHom_smooth (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup
    let H := toralLieSubalgebra ρ g.charts g.manifold g.lieGroup hSmooth
    ∀ (α : ι → H →ₗ[ℂ] ℂ),
      (∀ i, (α i).comp (complexifiedMapComplex f) =
        complexifiedMapComplex
          (weightCharacterDifferentialLinear (μ i) g.charts)) →
      ∀ h : H, (∀ i, α i h = 0) → h = 0 := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.lieGroup
  dsimp only
  intro α hCompat h hZero
  exact selected_image_characters_separate_of_real_span
    T g hClosed hImm hLee μ hSpan
    (selectedTorusDifferentialIntoH (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup)
    (selectedTorusDifferentialIntoH_complexified_surjective (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup)
    α hCompat h hZero

end
end QuaternionicSymmetry.ManifoldTwistorSelectedCharacterSeparation
