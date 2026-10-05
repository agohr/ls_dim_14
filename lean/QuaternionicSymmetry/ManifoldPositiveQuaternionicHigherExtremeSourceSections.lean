import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldPositiveQuaternionicExtremeFixedComplexDimensionAlternative
import QuaternionicSymmetry.ManifoldQuaternionicHigherComponentSourceSectionBound

/-! The no-four-dimensional-source extremal-component alternative now
consumes a lower-dimensional normalized holomorphic-homogeneity induction
hypothesis directly. In the higher branch it selects the actual induced
positive geometry and obtains two sections of the literal ambient contact
line on the *same* full-torus component. The four-real-dimensional kernel
branch remains only the independently checked small-complex-dimension
alternative. -/

namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicHigherExtremeSourceSections

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
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev V := E × EuclideanSpace ℝ (Fin 2)

/-- At an actual extremal weight: a point; a positive-dimensional fixed
component of complex dimension at most three over a four-real-dimensional
kernel base; or a strictly lower-dimensional induced positive geometry whose
normalized homogeneous twistor supplies at least two sections of the
literal ambient contact-line restriction on this full-torus component. -/
theorem normalized_extreme_component_point_small_or_higher_sections
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
      ∃ k : ℕ, ∃ H : FixedComponentAtlas (J (E := E))
        (liftedSet P.tangent T.imageSubgroup) z k,
        ∃ b : ℕ, ∃ B : ComplexSubmanifoldInput.CompatibleComplexAtlas
          (realEmbeddedAtlas P.tangent P.connection B₀ T.imageSubgroup H) b,
          k = 2*b ∧
          ((component P.tangent T z).Subsingleton ∨
            (∃ C : FixedComponentAtlas P.tangent
              (T.connectedKernelImage P.tangent μ) z.1 4,
              0 < b ∧ b ≤ 3) ∨
            (∃ m : ℕ, ∃ hm : 2 ≤ m, m < n ∧
              ∃ C₀ : FixedComponentAtlas P.tangent
                (T.connectedKernelImage P.tangent μ) z.1 (4*m),
                letI : NeZero (4*m) := ⟨by omega⟩
                letI := C₀.charts
                letI := C₀.manifold
                ∃ R : CompactConnectedPositiveQuaternionicKahlerGeometry
                  (E := EuclideanSpace ℝ (Fin (4*m)))
                  (M := FixedComponent P.tangent
                    (T.connectedKernelImage P.tangent μ) z.1),
                  ∃ hR : IsInducedQuaternionicGeometry
                    P.toPositiveQuaternionicKahlerGeometry
                    R.toPositiveQuaternionicKahlerGeometry Subtype.val,
                  ∃ zR : SphereBundleTotal R.tangent,
                  let p := ManifoldQuaternionicInducedTwistorMap.sphereTotalMap
                    P.toPositiveQuaternionicKahlerGeometry
                    R.toPositiveQuaternionicKahlerGeometry Subtype.val
                    C₀.inclusion_injective_derivative hR zR
                  p = z ∧
                  ∃ a : ℕ, ∃ H' : FixedComponentAtlas (J (E := E))
                    (liftedSet P.tangent T.imageSubgroup) p a,
                    ∃ b' : ℕ, ∃ B' : ComplexSubmanifoldInput.CompatibleComplexAtlas
                      (realEmbeddedAtlas P.tangent P.connection B₀
                        T.imageSubgroup H') b',
                      a = 2*b' ∧ 0 < b' ∧
                      (letI : ChartedSpace (EuclideanSpace ℂ (Fin b'))
                          ↥(component P.tangent T p) := B'.charts
                       2 ≤ Module.finrank ℂ
                         (GlobalSections 𝓘(ℂ,EuclideanSpace ℂ (Fin b'))
                           (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
                             𝓘(ℂ,EuclideanSpace ℂ (Fin b'))
                             (contactLineCore P.tangent P.connection CP.line)
                             (Subtype.val : ↥(component P.tangent T p) →
                               SphereBundleTotal P.tangent)
                             B'.inclusion_holomorphic))))) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI := B₀.charts
  intro z hz μ hchar hextreme hInduction
  obtain ⟨k,H,b,B,hkb,hAlternative⟩ :=
    normalized_extreme_component_point_or_small_or_higher
      (normalized_of_positive hNT) hKodaira hR3 hFinite hEigen hCircle hT4 hjet hfixedSource P
      hTwistorFixed hComplex hLee n hn hDim B₀ hScalar T hT hr
      z hz μ hchar hextreme
  refine ⟨k,H,b,B,hkb,?_⟩
  by_cases hpoint : (component P.tangent T z).Subsingleton
  · exact Or.inl hpoint
  have hNontrivial : (component P.tangent T z).Nontrivial :=
    Set.not_subsingleton_iff.mp hpoint
  rcases hAlternative with hpoint' | hsmall | hhigher
  · exact False.elim (hpoint hpoint')
  · exact Or.inr (Or.inl hsmall)
  · rcases hhigher with ⟨m,hm,hmLt,C₀,R,hR⟩
    have hNormHom := hInduction m hm hmLt C₀ R hR
    obtain ⟨zR,hzR,a,H',b',B',ha,hb',hSections⟩ :=
      higher_component_literal_ambient_sections_ge_two_of_sources
        P hR3 hBG hNT hKodaira hLeeOrbit hAutSource
        T z hz μ hchar m n hm C₀
        R hR B₀ CP hTwistorFixed hComplex hNontrivial hLee
        hNormHom hFinite
    exact Or.inr (Or.inr ⟨m,hm,hmLt,C₀,R,hR,zR,hzR,
      a,H',b',B',ha,hb',hSections⟩)

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicHigherExtremeSourceSections
