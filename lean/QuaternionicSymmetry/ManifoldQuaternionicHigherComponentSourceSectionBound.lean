import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldQuaternionicHigherComponentSectionBound
import QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiExactGeneratedAmple

/-! Source-selected lower-dimensional twistor data close the actual
higher-component restricted-section bound. The caller supplies normalized
holomorphic homogeneity from the lower-dimensional induction statement;
Nitta–Takeuchi selects the *unscaled* contact atlas/line, and the internal
same-line theorem provides both generation and ampleness. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHigherComponentSourceSectionBound

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicHigherComponentRestrictionGeometry
open ManifoldQuaternionicHigherComponentSectionBound
open ManifoldTwistorNittaTakeuchiPositiveRicciInput
open ManifoldTwistorNittaTakeuchiExactGeneratedAmple
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldTwistorFullAutomorphisms
open ManifoldRiemannianFixedComponentInput
open ManifoldRiemannianFixedTotalGeodesyInput
open ManifoldRiemannianFixedComponentGenericInput
open ManifoldRiemannianIsometryLieInput
open ManifoldTwistorSphereCore ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open QuaternionicSymmetry.GeneralSmoothMapSource
open GeneralHolomorphicTransitiveOrbitSource
open GeneralHolomorphicFullAutomorphismLieSource
open HolomorphicPositiveLineKodairaSource
open TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [PreconnectedSpace M]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

private abbrev J := 𝓘(ℝ,E).prod (𝓡 2)
private abbrev V := E × EuclideanSpace ℝ (Fin 2)

/-- The actual smaller positive geometry carries a source-selected
generated ample contact line; therefore the *same literal* non-point
full-torus component has at least two sections of the ambient contact-line
restriction. Neither a smaller atlas/contact choice nor generation or
ampleness of that line is a caller premise. -/
theorem higher_component_literal_ambient_sections_ge_two_of_sources
    (hR3 : IsometryLieSource.{0,0})
    (hBG : FixedComponentTotalGeodesyOnModel (E := E) (M := M))
    (hNT : PositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hLeeOrbit : LeeHolomorphicTransitiveOrbitSubmersion)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    {r : ℕ} (T : ContinuousTorusAction P.tangent r)
    (z : SphereBundleTotal P.tangent)
    (hz : ∀ t, T.representation t • z = z)
    (μ : Fin r → ℤ)
    (hchar : ∀ t, torusVerticalCircleCharacter P.tangent hR3 T z hz t =
      weightCharacter μ t)
    (m n : ℕ) (hm : 2 ≤ m)
    (C₀ : FixedComponentAtlas P.tangent
      (T.connectedKernelImage P.tangent μ) z.1 (4*m)) :
    letI : NeZero (4*m) := ⟨by omega⟩
    letI := C₀.charts
    letI := C₀.manifold
    ∀ (R : CompactConnectedPositiveQuaternionicKahlerGeometry
        (E := EuclideanSpace ℝ (Fin (4*m)))
        (M := FixedComponent P.tangent
          (T.connectedKernelImage P.tangent μ) z.1))
      (hR : IsInducedQuaternionicGeometry
        P.toPositiveQuaternionicKahlerGeometry
        R.toPositiveQuaternionicKahlerGeometry Subtype.val)
      (B : CompatibleComplexAtlas P.tangent P.connection n)
      (CP : HolomorphicContactData P.tangent P.connection n B)
      (hFixed : ManifoldQuaternionicTwistorFixedFromCompactAction.LiftedFixedComponents P.tangent)
      (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
      (hNontrivial : (component P.tangent T z).Nontrivial)
      (hLee : LeeEmbeddedCodomainRestrictionTheorem)
      (hNormHom : ∃ s : ℝ, ∃ hs : s ≠ 0,
        ∃ A : CompatibleComplexAtlas (rescaleMetric R.tangent s hs)
          (rescaleConnection R.tangent R.connection s hs) m,
          ∀ u v : SphereBundleTotal (rescaleMetric R.tangent s hs),
            ∃ f : TwistorHolomorphicAutomorphisms
              (rescaleMetric R.tangent s hs)
              (rescaleConnection R.tangent R.connection s hs) A,
              f.1 u = v)
      (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness),
      letI := B.charts
      ∃ zR : SphereBundleTotal R.tangent,
      let p := sphereTotalMap P.toPositiveQuaternionicKahlerGeometry
        R.toPositiveQuaternionicKahlerGeometry Subtype.val
        C₀.inclusion_injective_derivative hR zR
      p = z ∧
      ∃ a : ℕ, ∃ H : FixedComponentAtlas (J (E := E))
        (ManifoldQuaternionicTwistorLiftedFixedSet.liftedSet P.tangent
          T.imageSubgroup) p a,
        ∃ b : ℕ, ∃ C : ComplexSubmanifoldInput.CompatibleComplexAtlas
          (ManifoldQuaternionicTwistorComplexFixedAtlas.realEmbeddedAtlas
            P.tangent P.connection B T.imageSubgroup H) b,
          a = 2*b ∧ 0 < b ∧
          (letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
              ↥(component P.tangent T p) := C.charts
           2 ≤ Module.finrank ℂ
             (GlobalSections 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
               (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
                 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
                 (contactLineCore P.tangent P.connection CP.line)
                 (Subtype.val : ↥(component P.tangent T p) →
                   SphereBundleTotal P.tangent)
                 C.inclusion_holomorphic))) := by
  letI : NeZero (4*m) := ⟨by omega⟩
  letI := C₀.charts
  letI := C₀.manifold
  intro R hR B CP hFixed hComplex hNontrivial hLee hNormHom
    hFinite
  obtain ⟨zR,_,_,_,_⟩ := higher_component_restriction_geometry
    P hR3 hBG T z hz μ hchar m hm C₀ R hR
  letI : CompactSpace (FixedComponent P.tangent
      (T.connectedKernelImage P.tangent μ) z.1) := ⟨R.compact⟩
  letI : PreconnectedSpace (FixedComponent P.tangent
      (T.connectedKernelImage P.tangent μ) z.1) := ⟨R.connected⟩
  letI : Nonempty (FixedComponent P.tangent
      (T.connectedKernelImage P.tangent μ) z.1) := ⟨zR.1⟩
  obtain ⟨s,hs,A₀,hTrans⟩ := hNormHom
  obtain ⟨A,CR,hGen,hAmple⟩ := exists_actual_generated_ample_contact_core
    hNT hKodaira hLeeOrbit hAutSource R m hm (by simp) s hs A₀ hTrans
  exact higher_component_literal_ambient_sections_ge_two
    P hR3 hBG T z hz μ hchar m n hm C₀
    R hR A B CR.contact CP hFixed hComplex hNontrivial hLee
    hGen hFinite hAmple

end
end QuaternionicSymmetry.ManifoldQuaternionicHigherComponentSourceSectionBound
