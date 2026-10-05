import QuaternionicSymmetry.ManifoldQuaternionicContactEigenSectionVanishing
import QuaternionicSymmetry.ManifoldQuaternionicTorusContactSections
import QuaternionicSymmetry.HolomorphicLineCorePullbackSections

/-! Restriction of the actual, unpowered contact line to the literal full-torus
fixed component. A section of a different integral weight restricts to zero.
No extension or surjectivity of this restriction map is asserted. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactComponentRestriction

open ManifoldQuaternionicTorusAction ManifoldQuaternionicTorusContactSections
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldQuaternionicFixedWeightComponents
open ManifoldQuaternionicContactIsotropyScalar
open ManifoldQuaternionicIsometryContactSections
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open ManifoldRiemannianFixedComponentGenericInput
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicContactPowerSectionAction
open TorusWeightSeparation HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M] [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  {r : ℕ} (T : ContinuousTorusAction Q r)
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The actual linear restriction map to the original contact line on the
literal component `component Q T z`. The target contains all its global
sections, not just sections extending from the ambient twistor. -/
def contactRestriction
    (z : SphereBundleTotal Q)
    {b : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin b)) (↥(component Q T z))]
    (hIncl : letI := B.charts
      ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (Subtype.val : ↥(component Q T z) → SphereBundleTotal Q)) :
    letI := B.charts
    GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) →ₗ[ℂ]
      RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
        (Subtype.val : ↥(component Q T z) → SphereBundleTotal Q)
        hIncl := by
  letI := B.charts
  exact restrictionLinear 𝓘(ℂ,ComplexTwistorModel n)
    𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
    Subtype.val hIncl

/-- At an actual torus-fixed point, a nonzero unpowered eigensection has
the same integral weight as the contact-line fiber character. -/
theorem contactEigenSection_vanishes_if_weight_ne
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (η : Fin r → ℤ)
    (hEigen : letI := B.charts
      ∀ t, contactTorusRepresentation Q T D B C t s =
        (weightCharacter η t : ℂ) • s)
    (z : SphereBundleTotal Q) (hz : ∀ t, T.representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter Q hR3 T z hz t = weightCharacter ν t)
    (hne : η ≠ ν) : s z = 0 := by
  by_contra hs
  apply hne
  apply weight_eq_of_character_eq
  intro t
  apply Subtype.ext
  let ev : (letI := B.charts
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)) →
      SphereBundleTotal Q → ℂ := fun a x => a x
  have hImage : ev (contactTorusRepresentation Q T D B C t s)
      (sphereTotalMap Q (T.representation t) z) =
      contactScalar Q D C.line (T.representation t) z * ev s z := by
    have h := contactSectionEquiv_apply_at_image Q D B C (T.representation t) s z
    change ev (contactTorusRepresentation Q T D B C t s)
      (sphereTotalMap Q (T.representation t) z) =
      contactLineFiberEquiv Q D C.line (T.representation t) z (ev s z) at h
    have hlin := (contactLineFiberEquiv Q D C.line (T.representation t) z).map_smul
      (ev s z) (1 : ℂ)
    have hf : contactLineFiberEquiv Q D C.line (T.representation t) z (ev s z) =
        contactScalar Q D C.line (T.representation t) z * ev s z := by
      simpa only [smul_eq_mul, one_mul, contactScalar, mul_comm] using hlin
    exact h.trans hf
  have hz' : sphereTotalMap Q (T.representation t) z = z := hz t
  rw [hz'] at hImage
  have hValue : ev (contactTorusRepresentation Q T D B C t s) z =
      (weightCharacter η t : ℂ) * ev s z :=
    congrArg (fun a => ev a z) (hEigen t)
  have hc : contactScalar Q D C.line (T.representation t) z =
      (weightCharacter ν t : ℂ) := by
    rw [contactScalar_eq_verticalScalar Q D C.line z (T.representation t) (hz t)]
    exact congrArg (fun c : Circle => (c : ℂ)) (hν t)
  have hScalar : contactScalar Q D C.line (T.representation t) z =
      (weightCharacter η t : ℂ) := by
    apply mul_right_cancel₀ (show ev s z ≠ 0 from hs)
    exact hImage.symm.trans hValue
  exact hScalar.symm.trans hc

/-- Wrong-weight unpowered eigensections vanish at every point of the
selected literal component, using constancy of its actual fiber character. -/
theorem contactEigenSection_vanishes_on_component
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigenBasis : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (η : Fin r → ℤ)
    (hEigen : letI := B.charts
      ∀ t, contactTorusRepresentation Q T D B C t s =
        (weightCharacter η t : ℂ) • s)
    (z : SphereBundleTotal Q) (hz : ∀ t, T.representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter Q hR3 T z hz t = weightCharacter ν t)
    (hne : η ≠ ν) :
    ∀ w ∈ component Q T z, s w = 0 := by
  intro w hw
  have hwFixed : ∀ t, T.representation t • w = w :=
    (mem_fixedSpherePoints_iff_torus Q T w).mp
      (connectedComponentIn_subset _ _ hw)
  apply contactEigenSection_vanishes_if_weight_ne Q hR3 T D B C
    s η hEigen w hwFixed ν _ hne
  intro t
  exact (character_eq_on_component_of_ample Q hR3 hCircle T
    hFinite hEigenBasis D B C hAmple z hz w hw hwFixed t).trans (hν t)

/-- The actual restriction linear map kills every integral eigenvector
whose weight differs from the selected component's contact-line character.
Surjectivity is deliberately not part of this statement. -/
theorem contactRestriction_eigenSection_eq_zero
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigenBasis : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
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
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (η : Fin r → ℤ)
    (hEigen : letI := B.charts
      ∀ t, contactTorusRepresentation Q T D B C t s =
        (weightCharacter η t : ℂ) • s)
    (hne : η ≠ ν) :
    contactRestriction Q T D B C z hIncl s = 0 := by
  letI := B.charts
  apply ContMDiffSection.ext
  intro w
  exact contactEigenSection_vanishes_on_component Q hR3 T D B C
    hCircle hFinite hEigenBasis hAmple s η hEigen z hz ν hν hne w w.2

end
end QuaternionicSymmetry.ManifoldQuaternionicContactComponentRestriction
