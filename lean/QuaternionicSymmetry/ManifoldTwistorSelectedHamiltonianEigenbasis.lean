import QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianWeightSpaces
import QuaternionicSymmetry.ManifoldQuaternionicContactSectionsFromSources
import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusAction
import QuaternionicSymmetry.TorusLaurentRepresentation

/-! Integral eigenbasis weights on the SAME supplied contact twistor and
selected isometry torus are the actual Hamiltonian adjoint weights. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianEigenbasis

open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorUniqueContactHamiltonianEquivarianceFromSources
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorContactAutomorphismSections
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTorusContactSections
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicContactSectionsFromSources
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs CompactTorusEigenbasisSource TorusCharacterInput
open TorusLaurentRepresentation
open GeneralUniqueContactHamiltonianSource
open HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 200000

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
  [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The existing contact-section torus representation, not a newly
declared action, is exactly the selected-section operator family. -/
theorem selectedSectionOperator_eq_contactTorusRepresentation
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    {r : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (t : Torus r) :
    letI := A.charts
    selectedSectionOperator P n A C T t =
      contactTorusRepresentation P.tangent (actionOfEmbedding P.tangent T)
        P.connection A C.contact t := by
  letI := A.charts
  rw [selectedSectionOperator_eq_isometry]
  rfl

/-- Source-only eigenbasis on the already supplied `A,C`: each integral
eigenweight has a nonzero vector in the genuine derivative-adjoint weight
space, carried by the same canonical Hamiltonian equivalence. No new
twistor atlas or contact line is chosen. -/
theorem exists_selectedHamiltonian_eigenbasis_from_sources
    (hNTU : UniqueContactHamiltonianBijection)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hJoint :
      letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2))
    {r : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    ∃ b : Module.Basis
      (Fin (Module.finrank ℂ
        (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore P.tangent P.connection C.contact.line)))) ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line)),
      ∃ μ : Fin (Module.finrank ℂ
        (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore P.tangent P.connection C.contact.line))) → Fin r → ℤ,
        (∀ (t : Torus r) i,
          contactTorusRepresentation P.tangent (actionOfEmbedding P.tangent T)
            P.connection A C.contact t (b i) =
              (weightCharacter (μ i) t : ℂ) • b i) ∧
        (∀ t : Torus r,
          complexRepresentation b μ (compactInclusion r t) =
            contactTorusRepresentation P.tangent (actionOfEmbedding P.tangent T)
              P.connection A C.contact t) ∧
        (∀ i, (b i) ∈ selectedSectionWeightSpace P n A C T (μ i)) ∧
        ∀ i, ∃ v : V,
          v ∈ selectedAdjointWeightSpace (V := V) P n A C hPreserve T (μ i) ∧
          canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
            hNTU P n hn A C hPreserve hJoint v = b i ∧ v ≠ 0 := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  obtain ⟨b, μ, hEig⟩ := exists_integral_contact_eigenbasis_from_sources
    P.tangent hR3 hFinite hEigen hCircle
    (actionOfEmbedding P.tangent T) P.connection A C.contact
  have hMem (i) : (b i) ∈ selectedSectionWeightSpace P n A C T (μ i) := by
    intro t
    rw [selectedSectionOperator_eq_contactTorusRepresentation]
    exact hEig t i
  have hLaurent (t : Torus r) :
      complexRepresentation b μ (compactInclusion r t) =
        contactTorusRepresentation P.tangent (actionOfEmbedding P.tangent T)
          P.connection A C.contact t :=
    complexRepresentation_restrict b μ
      (contactTorusRepresentation P.tangent (actionOfEmbedding P.tangent T)
        P.connection A C.contact) hEig t
  refine ⟨b, μ, hEig, hLaurent, hMem, ?_⟩
  intro i
  let F := canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
    hNTU P n hn A C hPreserve hJoint
  let e := selectedHamiltonianWeightEquiv (V := V)
    hNTU P n hn A C hPreserve hJoint T (μ i)
  let w : selectedSectionWeightSpace P n A C T (μ i) := ⟨b i, hMem i⟩
  let v := e.symm w
  have hFv : F (v : V) = b i := congrArg Subtype.val (e.apply_symm_apply w)
  refine ⟨v.1, v.2, ?_, ?_⟩
  · exact hFv
  · intro hv
    have hb : b i = 0 := by
      calc
        b i = F (v : V) := hFv.symm
        _ = 0 := by rw [hv]; exact map_zero F
    exact (b.ne_zero i) hb

end
end QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianEigenbasis
