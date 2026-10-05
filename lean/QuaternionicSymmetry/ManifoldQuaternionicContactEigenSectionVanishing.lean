import QuaternionicSymmetry.ManifoldQuaternionicFixedWeightComponents

/-! A contact-power eigensection with a different weight vanishes at an
actual fixed point, hence along its connected fixed component. This is the
kernel-side restriction statement only; surjectivity onto all sections of
an extremal restriction is not inferred from it. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactEigenSectionVanishing

open ManifoldQuaternionicTorusAction ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicContactPowerWeights ManifoldQuaternionicContactPowerFixedWeights
open ManifoldQuaternionicContactPowerContinuity ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactIsotropyScalar TorusWeightSeparation
open ManifoldQuaternionicFixedWeightComponents ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses ManifoldTwistorSphereCore
open HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  {r : ℕ} (T : ContinuousTorusAction Q r)
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B) (k : ℕ)

theorem eigenSection_vanishes_if_weight_ne
    (s : letI := B.charts; PowerSections Q D B C k)
    (η : Fin r → ℤ)
    (hEigenSection : letI := B.charts
      ∀ t, contactPowerTorusRepresentation Q T D B C k t s =
        (weightCharacter η t : ℂ) • s)
    (z : SphereBundleTotal Q) (hz : ∀ t, T.representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter Q hR3 T z hz t = weightCharacter ν t)
    (hDifferent : η ≠ k • ν) : s z = 0 := by
  by_contra hsz
  apply hDifferent
  apply weight_eq_of_character_eq
  intro t
  apply Subtype.ext
  rw [weightCharacter_nsmul]
  change (weightCharacter η t : ℂ) = (weightCharacter ν t : ℂ) ^ k
  have hc : contactScalar Q D C.line (T.representation t) z =
      (weightCharacter ν t : ℂ) := by
    rw [contactScalar_eq_verticalScalar Q D C.line z (T.representation t) (hz t)]
    exact congrArg (fun c : Circle => (c : ℂ)) (hν t)
  rw [← hc]
  exact (fixedPoint_powerScalar_eq_eigencharacter Q T D B C k
    s η hEigenSection z hz hsz t).symm

theorem eigenSection_vanishes_on_component
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (s : letI := B.charts; PowerSections Q D B C k)
    (η : Fin r → ℤ)
    (hEigenSection : letI := B.charts
      ∀ t, contactPowerTorusRepresentation Q T D B C k t s =
        (weightCharacter η t : ℂ) • s)
    (z : SphereBundleTotal Q) (hz : ∀ t, T.representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter Q hR3 T z hz t = weightCharacter ν t)
    (hDifferent : η ≠ k • ν) :
    ∀ w ∈ component Q T z, s w = 0 := by
  intro w hw
  have hwFixed : ∀ t, T.representation t • w = w :=
    (mem_fixedSpherePoints_iff_torus Q T w).mp
      (connectedComponentIn_subset _ _ hw)
  apply eigenSection_vanishes_if_weight_ne Q hR3 T D B C k
    s η hEigenSection w hwFixed ν _ hDifferent
  intro t
  exact (character_eq_on_component_of_ample Q hR3 hCircle T
    hFinite hEigen D B C hAmple z hz w hw hwFixed t).trans (hν t)

end
end QuaternionicSymmetry.ManifoldQuaternionicContactEigenSectionVanishing
