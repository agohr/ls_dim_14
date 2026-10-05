import QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianToralBracketBasis

/-! Bracket characters of the actual selected contact-Lie eigenbasis agree
on every compact-torus differential generator with the differentiated
integral characters. No span or centre conclusion is assumed here. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedBracketCharacterFidelity

open ManifoldTwistorSelectedHamiltonianToralBracketBasis
open ManifoldTwistorSelectedAdjointBracketWeight
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
open CompactLieTorusInputs
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource
open GeneralDifferentiatedCharacterEigenvector
open ComplexLieToralDifferentialSubalgebra
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

theorem selected_bracket_character_generator_eq_integral_derivative
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
      P n A C hPreserve T (μ i))
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
    (i : ι) (w : letI := hTorusChart
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
    letI := hTorusManifold
    letI := hTorusLie
    let ρ := selectedContactTorusHom P n A C T
    let hSmooth := selectedContactTorusHom_smooth (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      hTorusChart hTorusManifold hTorusLie
    let H := toralLieSubalgebra ρ hTorusChart hTorusManifold hTorusLie hSmooth
    χ (⟨mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w,
      Submodule.subset_span (show
        mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w ∈
          differentialGenerators ρ hTorusChart from ⟨w,rfl⟩)⟩ : H) i =
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
        (fun t : Torus r => (weightCharacter (μ i) t : ℂ)) 1 w : ℂ) := by
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
  let s : GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w
  have hs : s ∈ differentialGenerators ρ hTorusChart := ⟨w,rfl⟩
  let h : H := ⟨s, Submodule.subset_span hs⟩
  let c : ℂ := mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
    (fun t : Torus r => (weightCharacter (μ i) t : ℂ)) 1 w
  have hEq := hBracket h i
  have hDiff := selectedAdjointWeight_bracket_generator (V := V)
    hBG9 hR3 hClosed hImm hLee P n A C hPreserve T (μ i)
    hTorusChart hTorusManifold hTorusLie (b i) (hWeight i) w
  have htransport {a z : ContactAutomorphisms
      P.tangent P.connection A C.contact.line} (haz : a = z)
      (u : TangentSpace 𝓘(ℝ,V) a) :
      (haz ▸ u : TangentSpace 𝓘(ℝ,V) z) = (u : V) := by
    cases haz
    rfl
  have h0 :
      (ρ.map_one ▸ mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w :
        TangentSpace 𝓘(ℝ,V)
          (1 : ContactAutomorphisms P.tangent P.connection A C.contact.line)) =
      (s : V) := htransport ρ.map_one _
  let Lc := GroupLieAlgebra 𝓘(ℂ,V)
    (ContactAutomorphisms P.tangent P.connection A C.contact.line)
  let br : Lc → Lc := fun x => @Bracket.bracket Lc Lc inferInstance x (b i)
  have hbr := congrArg br h0.symm
  have hScalar : tangentScalarSmul (V := V)
      ((weightCharacter (μ i) (1 : Torus r) : Circle) : ℂ) (b i : V)
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
        (fun t : Torus r => (weightCharacter (μ i) t : ℂ)) 1 w) =
      c • (b i : V) := by
    change c • (b i : V) = c • (b i : V)
    rfl
  have hDiff' : br s = c • (b i : Lc) := hbr.trans (hDiff.trans hScalar)
  have hEq' : br s = χ h i • (b i : Lc) := hEq
  have hScalarEq : χ h i = c :=
    smul_left_injective ℂ (b.ne_zero i) (hEq'.symm.trans hDiff')
  exact hScalarEq

end
end QuaternionicSymmetry.ManifoldTwistorSelectedBracketCharacterFidelity
