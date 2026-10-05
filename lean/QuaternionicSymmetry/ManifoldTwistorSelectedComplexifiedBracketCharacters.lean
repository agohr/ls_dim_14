import QuaternionicSymmetry.ManifoldTwistorSelectedTorusComplexifiedDifferential
import QuaternionicSymmetry.LieBracketEigencharacterLinear
import QuaternionicSymmetry.TorusWeightCharacterDifferentialLinear

/-! Honest complex-linear selected bracket characters and their exact
pullback along the actual complexified torus differential. The real
generator compatibility is explicit; the previous fidelity theorem
supplies it for the actual integral-weight basis. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedComplexifiedBracketCharacters

open ManifoldTwistorSelectedTorusComplexifiedDifferential
open LieBracketEigencharacterLinear
open RealCharacterComplexificationCompatibility
open RealToComplexTangentComplexification
open TorusWeightCharacterDifferentialLinear
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ComplexLieToralDifferentialSubalgebra
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M V ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem exists_selected_complexified_bracket_characters
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
    (χ :
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
      toralLieSubalgebra ρ hTorusChart hTorusManifold hTorusLie hSmooth → ι → ℂ)
    (hBracket :
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
      ∀ (h : H) i,
        @Bracket.bracket
          (GroupLieAlgebra 𝓘(ℂ,V)
            (ContactAutomorphisms P.tangent P.connection A C.contact.line))
          (GroupLieAlgebra 𝓘(ℂ,V)
            (ContactAutomorphisms P.tangent P.connection A C.contact.line))
          inferInstance (h : GroupLieAlgebra 𝓘(ℂ,V)
            (ContactAutomorphisms P.tangent P.connection A C.contact.line))
          (b i : GroupLieAlgebra 𝓘(ℂ,V)
            (ContactAutomorphisms P.tangent P.connection A C.contact.line)) =
        χ h i • (b i : GroupLieAlgebra 𝓘(ℂ,V)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line)))
    (hCompat :
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
      let f := selectedTorusDifferentialIntoH (V := V)
        hR3 hClosed hImm hLee P n A C hPreserve T
        hTorusChart hTorusManifold hTorusLie
      ∀ i w, χ (f w) i =
        (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
          (fun t : Torus r => (weightCharacter (μ i) t : ℂ)) 1 w : ℂ)) :
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
    let f := selectedTorusDifferentialIntoH (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      hTorusChart hTorusManifold hTorusLie
    let ρ := selectedContactTorusHom P n A C T
    let hSmooth := selectedContactTorusHom_smooth (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      hTorusChart hTorusManifold hTorusLie
    let H := toralLieSubalgebra ρ hTorusChart hTorusManifold hTorusLie hSmooth
    ∃ α : ι → (H →ₗ[ℂ] ℂ),
      (∀ i h, α i h = χ h i) ∧
      ∀ i,
        (α i).comp (complexifiedMapComplex f) =
          complexifiedMapComplex
            (weightCharacterDifferentialLinear (μ i) hTorusChart) := by
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
  let H := toralLieSubalgebra ρ hTorusChart hTorusManifold hTorusLie hSmooth
  let f := selectedTorusDifferentialIntoH (V := V)
    hR3 hClosed hImm hLee P n A C hPreserve T
    hTorusChart hTorusManifold hTorusLie
  let bG : Module.Basis ι ℂ (GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) := b
  let α := basisEigencharactersLinear H bG χ hBracket
  refine ⟨α, fun i h => rfl, ?_⟩
  intro i
  let β : (Fin d → ℝ) →ₗ[ℝ] ℂ :=
    weightCharacterDifferentialLinear (μ i) hTorusChart
  apply complexified_character_comp f (α i) β
  intro w
  exact hCompat i w

end
end QuaternionicSymmetry.ManifoldTwistorSelectedComplexifiedBracketCharacters
