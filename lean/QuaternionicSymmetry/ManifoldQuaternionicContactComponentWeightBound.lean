import QuaternionicSymmetry.ManifoldQuaternionicContactComponentRestriction
import QuaternionicSymmetry.ManifoldQuaternionicContactSectionsFromSources
import QuaternionicSymmetry.SurjectiveRestrictionWeightBound

/-! The actual unpowered contact restriction is supported on its component
weight space. Surjectivity remains an explicit geometric input. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactComponentWeightBound

open ManifoldQuaternionicContactComponentRestriction
open ManifoldQuaternionicContactSectionsFromSources
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTorusContactSections
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap TorusWeightSeparation
open SurjectiveRestrictionWeightBound
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M] [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  {r : ℕ} (T : ContinuousTorusAction Q r)
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

/-- The weight-`ν` submodule of the complete unpowered contact-line
section space, defined as the intersection of genuine action eigenspaces. -/
def contactWeightSubmodule (ν : Fin r → ℤ) :
    letI := B.charts
    Submodule ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.line)) := by
  letI := B.charts
  exact ⨅ t : Torus r,
    LinearMap.ker (contactTorusRepresentation Q T D B C t -
      (weightCharacter ν t : ℂ) • LinearMap.id)

theorem mem_contactWeightSubmodule_iff (ν : Fin r → ℤ)
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)) :
    s ∈ contactWeightSubmodule Q T D B C ν ↔
      ∀ t, contactTorusRepresentation Q T D B C t s =
        (weightCharacter ν t : ℂ) • s := by
  simp [contactWeightSubmodule, sub_eq_zero]

/-- If the literal restriction is surjective, its target has dimension at
most the selected character space. The proof uses only actual unpowered
sections, their integral eigenbasis, and checked wrong-weight vanishing. -/
theorem restricted_finrank_le_contactWeight
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (z : SphereBundleTotal Q) (hz : ∀ t, T.representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter Q hR3 T z hz t = weightCharacter ν t)
    {b : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin b)) (↥(component Q T z))]
    (hIncl : letI := B.charts
      ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (Subtype.val : ↥(component Q T z) → SphereBundleTotal Q))
    (hSurj : Function.Surjective (contactRestriction Q T D B C z hIncl)) :
    letI := B.charts
    Module.finrank ℂ (RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
      (Subtype.val : ↥(component Q T z) → SphereBundleTotal Q) hIncl) ≤
      Module.finrank ℂ (contactWeightSubmodule Q T D B C ν) := by
  letI := B.charts
  letI := ManifoldQuaternionicContactFiniteSections.finiteDimensional_contactSections
    Q hFinite D B C
  obtain ⟨basis, μ, hμ⟩ :=
    exists_integral_contact_eigenbasis_from_sources
      Q hR3 hFinite hEigen hCircle T D B C
  apply finrank_le_of_basis_mem_or_zero basis
    (contactWeightSubmodule Q T D B C ν)
    (contactRestriction Q T D B C z hIncl) hSurj
  intro i
  by_cases hi : μ i = ν
  · left
    apply (mem_contactWeightSubmodule_iff Q T D B C ν (basis i)).2
    intro t
    simpa only [hi] using hμ t i
  · right
    exact contactRestriction_eigenSection_eq_zero Q hR3 T D B C
      hCircle hFinite hEigen hAmple z hz ν hν hIncl
      (basis i) (μ i) (fun t => hμ t i) hi

end
end QuaternionicSymmetry.ManifoldQuaternionicContactComponentWeightBound
