import QuaternionicSymmetry.ManifoldQuaternionicContactComponentWeightOccurrence
import QuaternionicSymmetry.ManifoldTwistorSelectedComponentRestrictionBound

/-! The actual selected Hamiltonian contact-section weight occurs whenever
the same component has a nonzero restricted section and ambient restriction
is surjective. This precedes, and does not depend on, centre/root bounds. -/
namespace QuaternionicSymmetry.ManifoldTwistorSelectedComponentWeightOccurrence

open ManifoldQuaternionicContactComponentWeightOccurrence
open ManifoldQuaternionicContactComponentWeightBound
open ManifoldQuaternionicContactComponentRestriction
open ManifoldTwistorSelectedComponentRestrictionBound
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicSpanSymmetry
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
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
  {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)

/-- Genuine occurrence of the selected section weight, not merely a
formal convex-hull vertex. BWW-type extension surjectivity is visible. -/
theorem selectedSectionWeightSpace_ne_bot_of_nonzero_restriction
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
    (hTarget : letI := A.charts
      ∃ s : RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
          𝓘(ℂ,EuclideanSpace ℂ (Fin b))
          (contactLineCore P.tangent P.connection C.contact.line)
          (Subtype.val : ↥(component P.tangent
            (actionOfEmbedding P.tangent T) z) → SphereBundleTotal P.tangent)
          hIncl,
        s ≠ 0) :
    letI := A.charts
    selectedSectionWeightSpace P n A C T ν ≠ ⊥ := by
  letI := A.charts
  obtain ⟨s,hs,hEig⟩ := exists_nonzero_component_eigensection
    P.tangent (actionOfEmbedding P.tangent T) P.connection A C.contact
    hR3 hFinite hEigen hCircle hAmple z hz ν hν hIncl hSurj hTarget
  apply (Submodule.ne_bot_iff (selectedSectionWeightSpace P n A C T ν)).2
  refine ⟨s, ?_, hs⟩
  rw [← contactWeightSubmodule_eq_selected P n A C T ν]
  exact (mem_contactWeightSubmodule_iff P.tangent (actionOfEmbedding P.tangent T)
    P.connection A C.contact ν s).2 hEig

/-- The point branch supplies the nonzero restricted section internally;
only actual ambient extension surjectivity remains external. -/
theorem selectedSectionWeightSpace_ne_bot_of_point_component
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    (hAmple : letI := A.charts; letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (z : SphereBundleTotal P.tangent)
    (hz : ∀ t, (actionOfEmbedding P.tangent T).representation t • z = z)
    (hPoint : (component P.tangent (actionOfEmbedding P.tangent T) z).Subsingleton)
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
        P.connection A C.contact z hIncl)) :
    letI := A.charts
    selectedSectionWeightSpace P n A C T ν ≠ ⊥ := by
  letI := A.charts
  apply selectedSectionWeightSpace_ne_bot_of_nonzero_restriction
    P n A C T hR3 hFinite hEigen hCircle hAmple z hz ν hν hIncl hSurj
  exact point_component_has_nonzero_restricted_section P.tangent
    (actionOfEmbedding P.tangent T) P.connection A C.contact z hz hPoint hIncl

end
end QuaternionicSymmetry.ManifoldTwistorSelectedComponentWeightOccurrence
