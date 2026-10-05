import QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightRootFromAtlas
import QuaternionicSymmetry.NonzeroRootSpaceDimensionBound
import QuaternionicSymmetry.GeneralKillingRadicalSource
import QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianWeightSpaces

/-! The exact selected nonzero integral weight of the actual contact
Hamiltonian representation has multiplicity at most one once the SAME
selected toral algebra is Cartan and the contact Lie algebra is centre-
free with central radical. BG-L10 gives the Killing condition internally;
Mathlib's nonzero-root theorem supplies the one-dimensional bound. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightRootBound

open ManifoldTwistorSelectedNonzeroWeightRootFromAtlas
open NonzeroRootSpaceDimensionBound GeneralKillingRadicalSource
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ComplexLieToralDifferentialSubalgebra ComplexLieToralRootSpace
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicTorusAction ManifoldQuaternionicSpanSymmetry
open CompactLieTorusInputs
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource
open scoped Manifold ContDiff
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

set_option maxHeartbeats 800000 in
theorem selected_nonzero_weight_finrank_le_one_of_cartan_center
    (hBG9 : LeeRealAdjointDifferentialSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hNTU : GeneralUniqueContactHamiltonianSource.UniqueContactHamiltonianBijection)
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
    (hJoint : letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms
            P.tangent P.connection A × SphereBundleTotal P.tangent => p.1.1 p.2))
    [hQChart : ChartedSpace VR (QuaternionicIsometries P.tangent)]
    [hQManifold : IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent)]
    [hQLie : LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent)]
    [hQT2 : T2Space (QuaternionicIsometries P.tangent)]
    [hQSecond : SecondCountableTopology (QuaternionicIsometries P.tangent)]
    {r d : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (g : EmbeddedRealLieAtlas VR (Torus r)
      (QuaternionicIsometries P.tangent) T.hom d)
    (hCartan : letI := A.charts
      letI := A.complexManifold
      letI := contactCharts (V := V)
        P.tangent P.connection A C.contact.line hPreserve
      letI := contactManifold (V := V)
        P.tangent P.connection A C.contact.line hPreserve
      letI := contactLieGroup (V := V)
        P.tangent P.connection A C.contact.line hPreserve
      let H := toralLieSubalgebra (selectedContactTorusHom P n A C T)
        g.charts g.manifold g.lieGroup
        (selectedContactTorusHom_smooth (V := V)
          hR3 hClosed hImm hLee P n A C hPreserve T
          g.charts g.manifold g.lieGroup)
      H.IsCartanSubalgebra)
    (hKilling : letI := A.charts
      letI := A.complexManifold
      letI := contactCharts (V := V)
        P.tangent P.connection A C.contact.line hPreserve
      letI := contactLieGroup (V := V)
        P.tangent P.connection A C.contact.line hPreserve
      letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
        LieGroup.of_le (ENat.LEInfty.out)
      LieAlgebra.IsKilling ℂ
        (GroupLieAlgebra 𝓘(ℂ,V)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line)))
    (hCenter : letI := A.charts
      letI := A.complexManifold
      letI := contactCharts (V := V)
        P.tangent P.connection A C.contact.line hPreserve
      letI := contactLieGroup (V := V)
        P.tangent P.connection A C.contact.line hPreserve
      LieAlgebra.center ℂ (GroupLieAlgebra 𝓘(ℂ,V)
        (ContactAutomorphisms P.tangent P.connection A C.contact.line)) = ⊥)
    (μ : Fin r → ℤ) (hμ : μ ≠ 0) :
    Module.finrank ℂ (selectedSectionWeightSpace P n A C T μ) ≤ 1 := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    LieGroup.of_le (ENat.LEInfty.out)
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.lieGroup
  let H := toralLieSubalgebra (selectedContactTorusHom P n A C T)
    g.charts g.manifold g.lieGroup
    (selectedContactTorusHom_smooth (V := V)
      hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup)
  letI : H.IsCartanSubalgebra := hCartan
  letI : FiniteDimensional ℂ (GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) := by
    unfold GroupLieAlgebra TangentSpace
    infer_instance
  letI : LieAlgebra.IsKilling ℂ (GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) :=
    hKilling
  by_cases hW : selectedAdjointWeightSpace (V := V)
      P n A C hPreserve T μ = ⊥
  · rw [← selectedHamiltonianWeight_finrank_eq (V := V)
      hNTU P n hn A C hPreserve hJoint T μ, hW]
    simp
  · obtain ⟨α, hα, hIncl⟩ :=
      exists_selected_nonzero_weight_root_inclusion_from_atlas
        (V := V) hBG9 hR3 hClosed hImm hLee P n A C hPreserve
        T g μ hμ hW
    rw [← selectedHamiltonianWeight_finrank_eq (V := V)
      hNTU P n hn A C hPreserve hJoint T μ]
    exact finrank_le_one_of_le_nonzero_rootSpace H
      (selectedAdjointWeightSpace (V := V) P n A C hPreserve T μ)
      α hα hIncl

end
end QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightRootBound
