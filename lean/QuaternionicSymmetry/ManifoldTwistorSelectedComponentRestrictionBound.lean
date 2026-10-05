import QuaternionicSymmetry.ManifoldQuaternionicContactComponentWeightBound
import QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianEigenbasis

/-! The selected Hamiltonian section weight is literally the same
unpowered contact-section weight that survives restriction to an actual
full-torus fixed component. -/
namespace QuaternionicSymmetry.ManifoldTwistorSelectedComponentRestrictionBound

open ManifoldQuaternionicContactComponentRestriction
open ManifoldQuaternionicContactComponentWeightBound
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorSelectedHamiltonianEigenbasis
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTorusContactSections
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicLineCoreAmpleFiniteMap TorusWeightSeparation
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
  [CompactSpace M] [PreconnectedSpace M]
  [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
  (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
  {r : ℕ} (T : TorusEmbedding
    (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)

/-- No isomorphic replacement of either submodule: both are equal in the
same complete unpowered contact-section space, with the same torus action. -/
theorem contactWeightSubmodule_eq_selected (ν : Fin r → ℤ) :
    letI := A.charts
    contactWeightSubmodule P.tangent (actionOfEmbedding P.tangent T)
      P.connection A C.contact ν = selectedSectionWeightSpace P n A C T ν := by
  letI := A.charts
  apply Submodule.ext
  intro s
  rw [mem_contactWeightSubmodule_iff]
  change (∀ t, contactTorusRepresentation P.tangent
      (actionOfEmbedding P.tangent T) P.connection A C.contact t s =
        (weightCharacter ν t : ℂ) • s) ↔
    (∀ t, selectedSectionOperator P n A C T t s =
      (weightCharacter ν t : ℂ) • s)
  constructor <;> intro hs t
  · rw [selectedSectionOperator_eq_contactTorusRepresentation]
    exact hs t
  · have ht := hs t
    rw [selectedSectionOperator_eq_contactTorusRepresentation] at ht
    exact ht

/-- Actual restricted `h⁰ ≤ 1` on the same component, provided its
unpowered ambient restriction map is surjective and the checked selected
nonzero-weight estimate is supplied. -/
theorem restricted_finrank_le_one_of_selected_weight_bound
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    (hAmple : letI := A.charts; letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (z : SphereBundleTotal P.tangent)
    (hz : ∀ t, (actionOfEmbedding P.tangent T).representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter P.tangent hR3
      (actionOfEmbedding P.tangent T) z hz t = weightCharacter ν t)
    {b : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin b))
      (↥(component P.tangent (actionOfEmbedding P.tangent T) z))]
    (hIncl : letI := A.charts
      ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (Subtype.val : ↥(component P.tangent
          (actionOfEmbedding P.tangent T) z) → SphereBundleTotal P.tangent))
    (hSurj : Function.Surjective
      (contactRestriction P.tangent (actionOfEmbedding P.tangent T)
        P.connection A C.contact z hIncl))
    (hBound : letI := A.charts
      Module.finrank ℂ (selectedSectionWeightSpace P n A C T ν) ≤ 1) :
    letI := A.charts
    Module.finrank ℂ (RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,EuclideanSpace ℂ (Fin b))
      (contactLineCore P.tangent P.connection C.contact.line)
      (Subtype.val : ↥(component P.tangent
        (actionOfEmbedding P.tangent T) z) → SphereBundleTotal P.tangent)
      hIncl) ≤ 1 := by
  letI := A.charts
  have hWeight := restricted_finrank_le_contactWeight P.tangent
    (actionOfEmbedding P.tangent T) P.connection A C.contact
    hR3 hFinite hEigen hCircle hAmple z hz ν hν hIncl hSurj
  rw [contactWeightSubmodule_eq_selected P n A C T ν] at hWeight
  exact hWeight.trans hBound

end
end QuaternionicSymmetry.ManifoldTwistorSelectedComponentRestrictionBound
