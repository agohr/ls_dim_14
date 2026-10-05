import QuaternionicSymmetry.ManifoldQuaternionicContactComponentWeightBound
import QuaternionicSymmetry.HolomorphicLinePointSections

/-! Nonzero sections of the literal restricted contact line, together
with explicitly assumed extension surjectivity, force the component
character to occur in the ambient complete unpowered section action.
The point-component case has a nonzero restricted section internally. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactComponentWeightOccurrence

open ManifoldQuaternionicContactComponentRestriction
open ManifoldQuaternionicContactComponentWeightBound
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTorusContactSections
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open HolomorphicLinePointSections HolomorphicLineCoreAmpleFiniteMap
open TorusWeightSeparation
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

/-- A nonzero restricted section and actual extension surjectivity force
the selected character to occur in the complete ambient contact-section
representation. No root-space dimension or centre argument is used. -/
theorem exists_nonzero_component_eigensection
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
    (hSurj : Function.Surjective (contactRestriction Q T D B C z hIncl))
    (hTarget : letI := B.charts
      ∃ s : RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
          𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
          (Subtype.val : ↥(component Q T z) → SphereBundleTotal Q) hIncl,
        s ≠ 0) :
    letI := B.charts
    ∃ s : GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line),
      s ≠ 0 ∧ ∀ t, contactTorusRepresentation Q T D B C t s =
        (weightCharacter ν t : ℂ) • s := by
  letI := B.charts
  letI := ManifoldQuaternionicContactFiniteSections.finiteDimensional_contactSections
    Q hFinite D B C
  letI : Module.Finite ℂ (RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
      (Subtype.val : ↥(component Q T z) → SphereBundleTotal Q) hIncl) :=
    Module.Finite.of_surjective (contactRestriction Q T D B C z hIncl) hSurj
  have hRank := restricted_finrank_le_contactWeight Q T D B C
    hR3 hFinite hEigen hCircle hAmple z hz ν hν hIncl hSurj
  have hTargetPos : 0 < Module.finrank ℂ
      (RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
        (Subtype.val : ↥(component Q T z) → SphereBundleTotal Q) hIncl) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr hTarget
  obtain ⟨s,hs⟩ := (Module.finrank_pos_iff_exists_ne_zero.mp
    (hTargetPos.trans_le hRank) :
      ∃ s : contactWeightSubmodule Q T D B C ν, s ≠ 0)
  refine ⟨s, ?_, (mem_contactWeightSubmodule_iff Q T D B C ν s).mp s.2⟩
  intro hzero
  apply hs
  exact Subtype.ext hzero

/-- A singleton literal fixed component has a nonzero actual section of
the restricted contact line, regardless of ambient section extension. -/
theorem point_component_has_nonzero_restricted_section
    (z : SphereBundleTotal Q) (hz : ∀ t, T.representation t • z = z)
    (hPoint : (component Q T z).Subsingleton)
    {b : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin b)) (↥(component Q T z))]
    (hIncl : letI := B.charts
      ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (Subtype.val : ↥(component Q T z) → SphereBundleTotal Q)) :
    letI := B.charts
    ∃ s : RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
        (Subtype.val : ↥(component Q T z) → SphereBundleTotal Q) hIncl,
      s ≠ 0 := by
  letI := B.charts
  letI : Subsingleton (↥(component Q T z)) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    exact hPoint x.2 y.2
  have hzSet : z ∈ fixedSpherePoints Q T.imageSubgroup :=
    (mem_fixedSpherePoints_iff_torus Q T z).mpr hz
  let y : ↥(component Q T z) := ⟨z, mem_connectedComponentIn hzSet⟩
  let L := pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
    𝓘(ℂ,EuclideanSpace ℂ (Fin b))
    (contactLineCore Q D C.line)
    (Subtype.val : ↥(component Q T z) → SphereBundleTotal Q) hIncl
  obtain ⟨s,hs⟩ := globallyGenerated 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) L y
  refine ⟨s, ?_⟩
  intro hzero
  apply hs
  rw [hzero]
  rfl

/-- In the point branch, extension surjectivity alone supplies an actual
nonzero ambient eigensection of the component's character. -/
theorem point_component_has_nonzero_ambient_eigensection
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (z : SphereBundleTotal Q) (hz : ∀ t, T.representation t • z = z)
    (hPoint : (component Q T z).Subsingleton)
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
    ∃ s : GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line),
      s ≠ 0 ∧ ∀ t, contactTorusRepresentation Q T D B C t s =
        (weightCharacter ν t : ℂ) • s :=
  exists_nonzero_component_eigensection Q T D B C
    hR3 hFinite hEigen hCircle hAmple z hz ν hν hIncl hSurj
    (point_component_has_nonzero_restricted_section Q T D B C z hz hPoint hIncl)

end
end QuaternionicSymmetry.ManifoldQuaternionicContactComponentWeightOccurrence
