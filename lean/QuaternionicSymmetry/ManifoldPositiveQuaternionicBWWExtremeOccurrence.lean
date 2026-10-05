import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldQuaternionicBWWComponentOccurrence
import QuaternionicSymmetry.ManifoldPositiveQuaternionicHigherExtremeSourceSections
import QuaternionicSymmetry.ManifoldTwistorSelectedComponentRestrictionBound
import QuaternionicSymmetry.ManifoldPositiveQuaternionicExtremeFixedComplexDimensionAlternative
import QuaternionicSymmetry.ManifoldQuaternionicHigherComponentSourceSectionBound

/-! The no-four-dimensional-source extremal-component alternative now
consumes a lower-dimensional normalized holomorphic-homogeneity induction
hypothesis directly. In the higher branch it selects the actual induced
positive geometry and obtains two sections of the literal ambient contact
line on the *same* full-torus component. The four-real-dimensional kernel
branch remains only the independently checked small-complex-dimension
alternative. -/

namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicBWWExtremeOccurrence

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

theorem normalized_extreme_has_nonzero_ambient_eigensection
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
    (hT : T.Faithful) (hr : 2 ≤ r) :
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
      ∃ s : GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore P.tangent P.connection CP.line),
        s ≠ 0 ∧ ∀ t, contactTorusRepresentation P.tangent T P.connection B₀ CP t s =
          (weightCharacter μ t : ℂ) • s := by
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
  rcases hAlternative with hPoint | hSmall | hHigher
  · letI : ChartedSpace (EuclideanSpace ℂ (Fin b)) ↥(component P.tangent T z) := B.charts
    letI : IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞ ↥(component P.tangent T z) := B.manifold
    exact actual_extreme_nonzero_eigensection_from_component_alternative
      P.tangent P.connection B₀ CP T hBWW hR3 hFinite hEigen hCircle hLee
      (by omega) hAmple hPic hT z hz μ hchar hextreme B.inclusion_holomorphic
      (B.inclusion_injective_derivative _) (Or.inl hPoint)
  · obtain ⟨C,hb,hb3⟩ := hSmall
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b)) ↥(component P.tangent T z) := B.charts
    letI : IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞ ↥(component P.tangent T z) := B.manifold
    exact actual_extreme_nonzero_eigensection_from_component_alternative
      P.tangent P.connection B₀ CP T hBWW hR3 hFinite hEigen hCircle hLee
      (by omega) hAmple hPic hT z hz μ hchar hextreme B.inclusion_holomorphic
      (B.inclusion_injective_derivative _) (Or.inr (Or.inl ⟨hb,hb3⟩))
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
    exact actual_extreme_nonzero_eigensection_from_component_alternative
      P.tangent P.connection B₀ CP T hBWW hR3 hFinite hEigen hCircle hLee
      (by omega) hAmple hPic hT p hzp μ hcharp hextreme B'.inclusion_holomorphic
      (B'.inclusion_injective_derivative _) (Or.inr (Or.inr hSections))

theorem normalized_extreme_selectedSectionWeightSpace_ne_bot
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
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n B₀)
    (hAmple : letI := B₀.charts; letI := B₀.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore P.tangent P.connection C.contact.line))
    (hPic : letI := B₀.charts
      Function.Bijective (fun m : ℤ =>
        (Quotient.mk _ (contactLineCore P.tangent P.connection C.contact.line) :
          CoreClass.{0} (B := SphereBundleTotal P.tangent) 𝓘(ℂ,ComplexTwistorModel n)) ^ m))
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r) (hr : 2 ≤ r) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    letI := B₀.charts
    ∀ (z : SphereBundleTotal P.tangent)
      (hz : ∀ t, (actionOfEmbedding P.tangent T).representation t • z = z) (μ : Fin r → ℤ),
      (hchar : ∀ t, torusVerticalCircleCharacter P.tangent hR3 (actionOfEmbedding P.tangent T) z hz t =
        weightCharacter μ t) →
      (hextreme : (fun i => (μ i : ℝ)) ∈
        (convexHull ℝ (actualRealWeights P.tangent hR3 (actionOfEmbedding P.tangent T))).extremePoints ℝ) →
      (hInduction : ∀ (m : ℕ) (hm : 2 ≤ m), m < n →
        ∀ (C₀ : FixedComponentAtlas P.tangent
          ((actionOfEmbedding P.tangent T).connectedKernelImage P.tangent μ) z.1 (4*m)),
        letI : NeZero (4*m) := ⟨by omega⟩
        letI := C₀.charts
        letI := C₀.manifold
        ∀ (R : CompactConnectedPositiveQuaternionicKahlerGeometry
          (E := EuclideanSpace ℝ (Fin (4*m)))
          (M := FixedComponent P.tangent
            ((actionOfEmbedding P.tangent T).connectedKernelImage P.tangent μ) z.1)),
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
      selectedSectionWeightSpace P n B₀ C T μ ≠ ⊥ := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI := B₀.charts
  intro z hz μ hchar hextreme hInduction
  obtain ⟨s,hs,hEig⟩ := normalized_extreme_has_nonzero_ambient_eigensection
    hBWW hNT hKodaira hR3 hFinite hEigen hCircle
    hT4 hjet hfixedSource hBG hLeeOrbit hAutSource P
    hTwistorFixed hComplex hLee n hn hDim B₀ C.contact hAmple hPic hScalar
    (actionOfEmbedding P.tangent T) (actionOfEmbedding_faithful P.tangent T) hr
    z hz μ hchar hextreme hInduction
  apply (Submodule.ne_bot_iff (selectedSectionWeightSpace P n B₀ C T μ)).2
  refine ⟨s,?_,hs⟩
  rw [← contactWeightSubmodule_eq_selected P n B₀ C T μ]
  exact (mem_contactWeightSubmodule_iff P.tangent (actionOfEmbedding P.tangent T)
    P.connection B₀ C.contact μ s).2 hEig

/-- Package occurrence at literal fixed points in the exact all-vertex form
consumed by geometric centre separation. -/
theorem selected_extremal_vertices_occur_of_fixedpoint_occurrence
    (hR3 : IsometryLieSource.{0,0})
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (B₀ : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n B₀)
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hOccurs : letI : CompactSpace M := ⟨P.compact⟩
      letI : PreconnectedSpace M := ⟨P.connected⟩
      letI := B₀.charts
      ∀ (z : SphereBundleTotal P.tangent)
        (hz : ∀ t, (actionOfEmbedding P.tangent T).representation t • z = z)
        (ν : Fin r → ℤ),
        (∀ t, torusVerticalCircleCharacter P.tangent hR3
          (actionOfEmbedding P.tangent T) z hz t = weightCharacter ν t) →
        TorusIntegralVertexExposure.realWeight ν ∈
          (convexHull ℝ (actualRealWeights P.tangent hR3
            (actionOfEmbedding P.tangent T))).extremePoints ℝ →
        selectedSectionWeightSpace P n B₀ C T ν ≠ ⊥) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    letI := B₀.charts
    ∀ w ∈ (convexHull ℝ (actualRealWeights P.tangent hR3
      (actionOfEmbedding P.tangent T))).extremePoints ℝ,
      ∃ ν : Fin r → ℤ, TorusIntegralVertexExposure.realWeight ν = w ∧
        selectedSectionWeightSpace P n B₀ C T ν ≠ ⊥ := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI := B₀.charts
  intro w hw
  obtain ⟨ν,z,hz,hν,hReal⟩ := actual_extreme_has_fixed_point
    P.tangent hR3 (actionOfEmbedding P.tangent T) hw
  refine ⟨ν,hReal,hOccurs z hz ν hν ?_⟩
  change (fun i => (ν i : ℝ)) ∈ _
  rw [hReal]
  exact hw

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicBWWExtremeOccurrence
