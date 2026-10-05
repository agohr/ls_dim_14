import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldQuaternionicContactFixedWeightSpan
import QuaternionicSymmetry.ManifoldQuaternionicContactComponentWeightBound
import QuaternionicSymmetry.ManifoldQuaternionicBWWComponentOccurrence
import QuaternionicSymmetry.ManifoldPositiveQuaternionicHigherExtremeSourceSections
import QuaternionicSymmetry.ManifoldTwistorSelectedComponentRestrictionBound
import QuaternionicSymmetry.ManifoldPositiveQuaternionicExtremeFixedComplexDimensionAlternative
import QuaternionicSymmetry.ManifoldQuaternionicHigherComponentSourceSectionBound

/-! Actual extremal isolation conditional on the source-derived nonzero
unpowered contact-section weight bound. The lower-dimensional normalized
homogeneity induction supplies literal restricted sections in the higher
branch; BWW supplies the same component's restriction surjection and small
lower bound. The four-real-dimensional branch uses only the existing small
complex-dimensional alternative. No four-dimensional twistor input occurs. -/

namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicBWWExtremeIsolation

open ManifoldPositiveQuaternionicExtremeFixedComplexDimensionAlternative
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicTorusAction ManifoldQuaternionicActualWeightHull
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldQuaternionicHigherComponentSourceSectionBound
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldTwistorFullAutomorphisms
open ManifoldRiemannianFixedComponentInput ManifoldRiemannianFixedComponentGenericInput
open ManifoldRiemannianFixedTotalGeodesyInput ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicSubmanifoldInput ManifoldTwistorSphereCore
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorNittaTakeuchiPositiveRicciInput
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicPositiveLineKodairaSource
open ProjectiveAnalyticAlgebraicSources CompactTorusEigenbasisSource TorusCharacterInput
open QuaternionicSymmetry.GeneralSmoothMapSource
open GeneralHolomorphicTransitiveOrbitSource
open GeneralHolomorphicFullAutomorphismLieSource
open scoped Manifold ContDiff
open ManifoldQuaternionicBWWComponentOccurrence GeneralBWWAnalyticExtremalSource
open ManifoldQuaternionicContactPowerSectionAction
open HolomorphicLineCoreAmpleFiniteMap ManifoldQuaternionicTorusContactSections
open ManifoldTwistorSelectedHamiltonianWeightSpaces ManifoldTwistorSelectedComponentRestrictionBound
open ManifoldQuaternionicContactComponentWeightBound CompactLieTorusInputs
open ManifoldQuaternionicMaximalTorusAction ManifoldQuaternionicSpanSymmetry
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev V := E × EuclideanSpace ℝ (Fin 2)

theorem normalized_extreme_component_is_point_of_weight_bound
    (hBWW : AnalyticExtremalRestrictionAndSmallSections)
    (hNT : PositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hR3 : IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (hT4 : PositiveQuaternionicSubmanifoldSource)
    (hjet : ManifoldRiemannianOneJetInput.RiemannianOneJetRigidityOnModel
      (E := E) (M := M))
    (hfixedSource : RiemannianFixedComponentOnModel (E := E) (M := M))
    (hBG : FixedComponentTotalGeodesyOnModel (E := E) (M := M))
    (hLeeOrbit : LeeHolomorphicTransitiveOrbitSubmersion)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hTwistorFixed : ManifoldQuaternionicTwistorFixedFromCompactAction.LiftedFixedComponents P.tangent)
    (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (B₀ : CompatibleComplexAtlas P.tangent P.connection n)
    (CP : HolomorphicContactData P.tangent P.connection n B₀)
    (hAmple : letI := B₀.charts; letI := B₀.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore P.tangent P.connection CP.line))
    (hPic : letI := B₀.charts
      Function.Bijective (fun m : ℤ =>
        (Quotient.mk _ (contactLineCore P.tangent P.connection CP.line) :
          CoreClass.{0} (B := SphereBundleTotal P.tangent) 𝓘(ℂ,ComplexTwistorModel n)) ^ m))
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (T : ContinuousTorusAction P.tangent r)
    (hT : T.Faithful) (hr : 2 ≤ r)
    (hWeightBound : letI : CompactSpace M := ⟨P.compact⟩
      letI : PreconnectedSpace M := ⟨P.connected⟩
      letI : LocallyCompactSpace M := inferInstance
      letI := B₀.charts
      ∀ ν : Fin r → ℤ, ν ≠ 0 →
        Module.finrank ℂ (ManifoldQuaternionicContactComponentWeightBound.contactWeightSubmodule
          P.tangent T P.connection B₀ CP ν) ≤ 1) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    letI := B₀.charts
    ∀ (z : SphereBundleTotal P.tangent)
      (hz : ∀ t, T.representation t • z = z) (μ : Fin r → ℤ),
      (hchar : ∀ t, torusVerticalCircleCharacter P.tangent hR3 T z hz t =
        weightCharacter μ t) →
      (hextreme : (fun i => (μ i : ℝ)) ∈
        (convexHull ℝ (actualRealWeights P.tangent hR3 T)).extremePoints ℝ) →
      (hInduction : ∀ (m : ℕ) (hm : 2 ≤ m), m < n →
        ∀ (C₀ : FixedComponentAtlas P.tangent
          (T.connectedKernelImage P.tangent μ) z.1 (4*m)),
        letI : NeZero (4*m) := ⟨by omega⟩
        letI := C₀.charts
        letI := C₀.manifold
        ∀ (R : CompactConnectedPositiveQuaternionicKahlerGeometry
          (E := EuclideanSpace ℝ (Fin (4*m)))
          (M := FixedComponent P.tangent
            (T.connectedKernelImage P.tangent μ) z.1)),
          IsInducedQuaternionicGeometry
            P.toPositiveQuaternionicKahlerGeometry
            R.toPositiveQuaternionicKahlerGeometry Subtype.val →
          ∃ s : ℝ, ∃ hs : s ≠ 0,
            ∃ A : CompatibleComplexAtlas (rescaleMetric R.tangent s hs)
              (rescaleConnection R.tangent R.connection s hs) m,
              ∀ u v : SphereBundleTotal (rescaleMetric R.tangent s hs),
                ∃ f : TwistorHolomorphicAutomorphisms
                  (rescaleMetric R.tangent s hs)
                  (rescaleConnection R.tangent R.connection s hs) A,
                  f.1 u = v) →
      (component P.tangent T z).Subsingleton := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI := B₀.charts
  letI := B₀.complexManifold
  letI := B₀.realManifold
  intro z hz μ hchar hextreme hInduction
  obtain ⟨k,H,b,B,hkb,hAlternative⟩ :=
    ManifoldPositiveQuaternionicHigherExtremeSourceSections.normalized_extreme_component_point_small_or_higher_sections
      hNT hKodaira hR3 hFinite hEigen hCircle
      hT4 hjet hfixedSource hBG hLeeOrbit hAutSource P
      hTwistorFixed hComplex hLee n hn hDim B₀ CP hScalar T hT hr
      z hz μ hchar hextreme hInduction
  have hSpan := ManifoldQuaternionicContactFixedWeightSpan.actualRealWeights_span_eq_top_from_sources
    P.tangent hR3 hFinite hEigen hCircle T hT
    P.connection B₀ CP hAmple
  have hAff := ManifoldQuaternionicContactFixedWeightSpan.actualRealWeights_affineSpan_of_span
    P.tangent hR3 T (by omega : 0 < r) hSpan
  have hNonzero := actual_extreme_ne_zero P.tangent hR3 T (by omega : 0 < r) hAff hextreme
  have hμ0 : μ ≠ 0 := by
    intro heq
    apply hNonzero
    funext i
    simp [heq]
  rcases hAlternative with hPoint | hSmall | hHigher
  · exact hPoint
  · obtain ⟨C,hb,hb3⟩ := hSmall
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b)) ↥(component P.tangent T z) := B.charts
    letI : IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞ ↥(component P.tangent T z) := B.manifold
    obtain ⟨hSurj,hLower⟩ :=
      ManifoldQuaternionicBWWExtremalApplication.actual_extremal_restriction_and_small_sections_from_sources
        P.tangent P.connection B₀ CP T hBWW hR3 hFinite hEigen hCircle hLee
        (by omega) hAmple hPic hT z hz μ hchar hextreme B.inclusion_holomorphic
        (B.inclusion_injective_derivative _)
    have hUpper := ManifoldQuaternionicContactComponentWeightBound.restricted_finrank_le_contactWeight
      P.tangent T P.connection B₀ CP hR3 hFinite hEigen hCircle hAmple
      z hz μ hchar B.inclusion_holomorphic hSurj
    have hTwo := hLower hb hb3
    have hOne := hUpper.trans (hWeightBound μ hμ0)
    omega
  · obtain ⟨m,hm,hmLt,C₀,R,hR,zR,hp,a,H',b',B',ha,hb',hSections⟩ := hHigher
    letI : NeZero (4*m) := ⟨by omega⟩
    letI := C₀.charts
    letI := C₀.manifold
    let p := ManifoldQuaternionicInducedTwistorMap.sphereTotalMap
      P.toPositiveQuaternionicKahlerGeometry R.toPositiveQuaternionicKahlerGeometry
      Subtype.val C₀.inclusion_injective_derivative hR zR
    change p = z at hp
    have hzp : ∀ t, T.representation t • p = p := by
      intro t
      rw [hp]
      exact hz t
    have hcharp : ∀ t, torusVerticalCircleCharacter P.tangent hR3 T p hzp t =
        weightCharacter μ t := by
      intro t
      simpa only [hp] using hchar t
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b')) ↥(component P.tangent T p) := B'.charts
    letI : IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b')) ∞ ↥(component P.tangent T p) := B'.manifold
    obtain ⟨hSurj,_⟩ :=
      ManifoldQuaternionicBWWExtremalApplication.actual_extremal_restriction_and_small_sections_from_sources
        P.tangent P.connection B₀ CP T hBWW hR3 hFinite hEigen hCircle hLee
        (by omega) hAmple hPic hT p hzp μ hcharp hextreme B'.inclusion_holomorphic
        (B'.inclusion_injective_derivative _)
    have hUpper := ManifoldQuaternionicContactComponentWeightBound.restricted_finrank_le_contactWeight
      P.tangent T P.connection B₀ CP hR3 hFinite hEigen hCircle hAmple
      p hzp μ hcharp B'.inclusion_holomorphic hSurj
    have hOne := hUpper.trans (hWeightBound μ hμ0)
    change 2 ≤ Module.finrank ℂ
      (RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,EuclideanSpace ℂ (Fin b'))
        (contactLineCore P.tangent P.connection CP.line)
        (Subtype.val : ↥(component P.tangent T p) → SphereBundleTotal P.tangent)
        B'.inclusion_holomorphic) at hSections
    omega

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicBWWExtremeIsolation
