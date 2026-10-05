import QuaternionicSymmetry.ManifoldQuaternionicBWWExtremalApplication
import QuaternionicSymmetry.ManifoldQuaternionicContactComponentWeightOccurrence

/-! Actual unpowered vertex occurrence from the point/small/higher section
alternative. Neither centre zero nor root multiplicity appears, so occurrence
can safely be used to prove centre zero. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicBWWComponentOccurrence
open GeneralBWWAnalyticExtremalSource ManifoldQuaternionicBWWExtremalApplication
open ManifoldQuaternionicContactComponentWeightOccurrence
open ManifoldQuaternionicContactComponentRestriction
open ManifoldQuaternionicTorusFixedComplexComponent ManifoldQuaternionicActualWeightHull
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLineCoreClasses HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap TorusLaurentRepresentation TorusIntegralVertexExposure
open ManifoldQuaternionicContactPowerSectionAction ManifoldQuaternionicTorusContactSections
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M] [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)
  {r : ℕ} (A : ContinuousTorusAction Q r)
  (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q))
  (hJoint : letI := B.charts
    ContMDiff (𝓘(ℂ,Fin r → ℂ).prod 𝓘(ℂ,ComplexTwistorModel n))
      𝓘(ℂ,ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal Q),
    ρ (compactInclusion r t) z = sphereTotalMap Q (A.representation t) z)



theorem actual_extreme_nonzero_eigensection_from_component_alternative
    (hBWW : AnalyticExtremalRestrictionAndSmallSections)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    (hLee : GeneralSmoothMapSource.LeeEmbeddedCodomainRestrictionTheorem)
    (hr : 0 < r)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (hPic : letI := B.charts
      Function.Bijective (fun m : ℤ =>
        (Quotient.mk _ (contactLineCore Q D C.line) :
          CoreClass.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n)) ^ m))
    (hFaithful : A.Faithful)
    (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter Q hR3 A z hz t = weightCharacter ν t)
    (hExt : realWeight ν ∈ (convexHull ℝ (actualRealWeights Q hR3 A)).extremePoints ℝ)
    {b : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin b)) (↥(component Q A z))]
    [IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞ (↥(component Q A z))]
    (hIncl : letI := B.charts
      ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) 𝓘(ℂ,ComplexTwistorModel n) ∞
        (Subtype.val : ↥(component Q A z) → SphereBundleTotal Q))
    (hImm : letI := B.charts
      ∀ y, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin b))
        𝓘(ℝ,ComplexTwistorModel n)
        (Subtype.val : ↥(component Q A z) → SphereBundleTotal Q) y))
    (hAlternative : letI := B.charts
      (component Q A z).Subsingleton ∨
      (0 < b ∧ b ≤ 3) ∨
      2 ≤ Module.finrank ℂ
        (RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
          𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
          (Subtype.val : ↥(component Q A z) → SphereBundleTotal Q) hIncl)) :
    letI := B.charts
    ∃ s : GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line),
      s ≠ 0 ∧ ∀ t, contactTorusRepresentation Q A D B C t s =
        (weightCharacter ν t : ℂ) • s := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨hSurj,hSmall⟩ := actual_extremal_restriction_and_small_sections_from_sources
    Q D B C A hBWW hR3 hFinite hEigen hCircle hLee
    hr hAmple hPic hFaithful z hz ν hν hExt hIncl hImm
  have hTarget : ∃ s : RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,EuclideanSpace ℂ (Fin b)) (contactLineCore Q D C.line)
      (Subtype.val : ↥(component Q A z) → SphereBundleTotal Q) hIncl, s ≠ 0 := by
    rcases hAlternative with hPoint | hSmallDim | hHigher
    · exact point_component_has_nonzero_restricted_section Q A D B C z hz hPoint hIncl
    · have hBound := hSmall hSmallDim.1 hSmallDim.2
      letI := Module.nontrivial_of_finrank_pos (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hBound)
      exact exists_ne 0
    · letI := Module.nontrivial_of_finrank_pos (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hHigher)
      exact exists_ne 0
  exact ManifoldQuaternionicContactComponentWeightOccurrence.exists_nonzero_component_eigensection
    Q A D B C hR3 hFinite hEigen hCircle hAmple z hz ν hν hIncl hSurj hTarget

end
end QuaternionicSymmetry.ManifoldQuaternionicBWWComponentOccurrence
