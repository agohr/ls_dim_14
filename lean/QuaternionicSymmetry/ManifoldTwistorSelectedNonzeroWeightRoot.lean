import QuaternionicSymmetry.ManifoldTwistorSelectedAdjointWeightRootInclusion
import QuaternionicSymmetry.SelectedIntegralCharacterDerivativeFromExp
import QuaternionicSymmetry.ToralRootEigenvalueUniqueness

/-! A nonzero selected integral character gives a nonzero actual root
character for the SAME root space containing the whole selected adjoint
weight space, provided the existing selected-atlas coordinate
exponential is smooth. No Cartan or multiplicity conclusion is used. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightRoot

open ManifoldTwistorSelectedAdjointWeightRootInclusion
open ManifoldTwistorSelectedAdjointBracketWeight
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ComplexLieToralDifferentialSubalgebra ComplexLieToralRootSpace
open SelectedIntegralCharacterDerivativeFromExp
open ToralRootEigenvalueUniqueness
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource
open SelectedTorusCompactExponentialSmooth
open GeneralDifferentiatedCharacterEigenvector
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem exists_selected_nonzero_weight_root_inclusion_of_exp
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
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hTorusChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hTorusManifold : letI := hTorusChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hTorusLie : letI := hTorusChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hExp : letI := hTorusChart
      ContMDiff 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin d → ℝ) ∞ (circleExpPi r))
    (hW : selectedAdjointWeightSpace (V := V)
      P n A C hPreserve T μ ≠ ⊥) :
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
    letI := toralLie_isNilpotent ρ hTorusChart hTorusManifold hTorusLie hSmooth
    ∃ α : H → ℂ, α ≠ 0 ∧
      selectedAdjointWeightSpace (V := V) P n A C hPreserve T μ ≤
        (LieAlgebra.rootSpace H α).toSubmodule := by
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
  let H := toralLieSubalgebra (V := V) ρ hTorusChart hTorusManifold hTorusLie hSmooth
  letI := toralLie_isNilpotent (V := V) ρ hTorusChart hTorusManifold hTorusLie hSmooth
  let W : Submodule ℂ (GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) :=
    selectedAdjointWeightSpace (V := V) P n A C hPreserve T μ
  obtain ⟨α, hIncl⟩ := exists_selected_weight_root_inclusion (V := V)
    hBG9 hR3 hClosed hImm hLee P n A C hPreserve T μ
    hTorusChart hTorusManifold hTorusLie hW
  obtain ⟨v₀, hv₀, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hχnz := weightCharacter_mfderiv_ne_zero_of_exp μ hμ
    hTorusChart hTorusManifold hTorusLie hClosed hImm hLee hExp
  obtain ⟨w, hw⟩ : ∃ w : GroupLieAlgebra 𝓘(ℝ,Fin d → ℝ) (Torus r),
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
        (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 w) ≠ 0 := by
    by_contra hn
    apply hχnz
    ext w
    have hw0 := not_exists.mp hn w
    simpa using not_not.mp hw0
  let c : ℂ := mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
    (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 w
  let s : H := ⟨mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w,
    Submodule.subset_span ⟨w,rfl⟩⟩
  have hbr := selectedAdjointWeight_bracket_generator (V := V)
    hBG9 hR3 hClosed hImm hLee P n A C hPreserve T μ
    hTorusChart hTorusManifold hTorusLie v₀ hv₀ w
  have htransport {a b : ContactAutomorphisms
      P.tangent P.connection A C.contact.line} (hab : a = b)
      (u : TangentSpace 𝓘(ℝ,V) a) :
      (hab ▸ u : TangentSpace 𝓘(ℝ,V) b) = (u : V) := by
    cases hab
    rfl
  have h0 :
      (ρ.map_one ▸ mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w :
        TangentSpace 𝓘(ℝ,V)
          (1 : ContactAutomorphisms P.tangent P.connection A C.contact.line)) =
        (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w : V) :=
    htransport ρ.map_one _
  let Lc := GroupLieAlgebra 𝓘(ℂ,V)
    (ContactAutomorphisms P.tangent P.connection A C.contact.line)
  let br : Lc → Lc := fun x => @Bracket.bracket Lc Lc inferInstance x v₀
  have hbrCast := congrArg br h0.symm
  have hscalar : tangentScalarSmul (V := V)
      ((weightCharacter μ (1 : Torus r) : Circle) : ℂ) (v₀ : V)
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
        (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 w) = c • (v₀ : V) := rfl
  have hEig : @Bracket.bracket Lc Lc inferInstance (s : Lc) v₀ = c • v₀ :=
    hbrCast.trans (hbr.trans hscalar)
  have hroot : v₀ ∈ LieAlgebra.rootSpace H α := hIncl hv₀
  have hαval : α s = c := root_value_eq_of_exact_eigenvector H α s v₀
    hroot hv₀ne c hEig
  refine ⟨α, ?_, hIncl⟩
  intro hαzero
  apply hw
  have hzero := congrFun hαzero s
  simpa [c, hαval] using hzero

end
end QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightRoot
