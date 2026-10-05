import QuaternionicSymmetry.ManifoldTwistorSelectedComplexifiedBracketCharacters

/-! Same-witness source-only complex-linear bracket characters on the
actual selected toral H. Their pullbacks along the complexified actual
torus differential are literally the complexifications of the integral
character derivatives. Full-dual span remains a separate hypothesis. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedComplexifiedCharactersFromSources

open ManifoldTwistorSelectedComplexifiedBracketCharacters
open ManifoldTwistorSelectedBracketBasisFidelityFromSources
open ManifoldTwistorSelectedTorusComplexifiedDifferential
open TorusWeightCharacterDifferentialLinear
open RealToComplexTangentComplexification
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs CompactTorusEigenbasisSource TorusCharacterInput
open GeneralUniqueContactHamiltonianSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource
open ComplexLieToralDifferentialSubalgebra
open HolomorphicLineCorePullback
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
  [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem exists_selected_complexified_characters_from_sources
    (hNTU : UniqueContactHamiltonianBijection)
    (hBG9 : LeeRealAdjointDifferentialSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hAutChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hJoint :
      letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2))
    {r d : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (hTorusChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hTorusManifold : letI := hTorusChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hTorusLie : letI := hTorusChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r)) :
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
    let J := Fin (Module.finrank ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line)))
    let f := selectedTorusDifferentialIntoH (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      hTorusChart hTorusManifold hTorusLie
    let ρ := selectedContactTorusHom P n A C T
    let hSmooth := selectedContactTorusHom_smooth (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      hTorusChart hTorusManifold hTorusLie
    let H := toralLieSubalgebra ρ hTorusChart hTorusManifold hTorusLie hSmooth
    ∃ b : Module.Basis J ℂ V,
      ∃ μ : J → Fin r → ℤ,
      ∃ α : J → (H →ₗ[ℂ] ℂ),
        (∀ i, b i ∈ selectedAdjointWeightSpace (V := V)
          P n A C hPreserve T (μ i)) ∧
        (∀ (h : H) i,
          @Bracket.bracket
            (GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line))
            (GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line))
            inferInstance
            (h : GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line))
            (b i : GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line)) =
            α i h • (b i : GroupLieAlgebra 𝓘(ℂ,V)
              (ContactAutomorphisms P.tangent P.connection A C.contact.line))) ∧
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
  obtain ⟨b, μ, χ, hWeight, hBracket, hFidelity⟩ :=
    exists_selectedHamiltonian_bracket_basis_with_character_fidelity (V := V)
      hNTU hBG9 hR3 hClosed hImm hLee hFinite hEigen hCircle
      P n hn A C hPreserve hJoint T hTorusChart hTorusManifold hTorusLie
  have hCompat :
      let f := selectedTorusDifferentialIntoH (V := V)
        hR3 hClosed hImm hLee P n A C hPreserve T
        hTorusChart hTorusManifold hTorusLie
      ∀ i w, χ (f w) i =
        (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
          (fun t : Torus r => (weightCharacter (μ i) t : ℂ)) 1 w : ℂ) := by
    dsimp only
    intro i w
    exact hFidelity i w
  obtain ⟨α, hα, hComplex⟩ :=
    exists_selected_complexified_bracket_characters (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      hTorusChart hTorusManifold hTorusLie b μ χ hBracket hCompat
  refine ⟨b, μ, α, hWeight, ?_, hComplex⟩
  intro h i
  rw [hα i h]
  exact hBracket h i

end
end QuaternionicSymmetry.ManifoldTwistorSelectedComplexifiedCharactersFromSources
