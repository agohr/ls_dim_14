import QuaternionicSymmetry.ManifoldQuaternionicHigherComponentRestrictionGeometry
import QuaternionicSymmetry.ManifoldQuaternionicTorusStrictSectionBound

/-! The higher-dimensional branch of the actual extremal fixed-component
alternative feeds the established intrinsic-to-literal-ambient restriction
estimate. The smaller intrinsic contact line is the only line assumed to be
globally generated. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHigherComponentSectionBound

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicHigherComponentRestrictionGeometry
open ManifoldQuaternionicTorusStrictSectionBound
open ManifoldRiemannianFixedComponentInput
open ManifoldRiemannianFixedTotalGeodesyInput
open ManifoldRiemannianFixedComponentGenericInput
open ManifoldRiemannianIsometryLieInput
open ManifoldTwistorSphereCore
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap
open QuaternionicSymmetry.GeneralSmoothMapSource
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

/-- On the *same* literal non-point full-torus component, the contact line
restricted from the ambient twistor has at least two sections. The smaller
contact line's generation and ampleness remain explicit until supplied by
the lower-dimensional induction hypothesis and T1/Kodaira construction. -/
theorem higher_component_literal_ambient_sections_ge_two
    (hR3 : IsometryLieSource.{0,0})
    (hBG : FixedComponentTotalGeodesyOnModel (E := E) (M := M))
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
      (A : CompatibleComplexAtlas R.tangent R.connection m)
      (B : CompatibleComplexAtlas P.tangent P.connection n)
      (CR : HolomorphicContactData R.tangent R.connection m A)
      (CP : HolomorphicContactData P.tangent P.connection n B)
      (hFixed : ManifoldQuaternionicTwistorFixedFromCompactAction.LiftedFixedComponents P.tangent)
      (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
      (hNontrivial : (component P.tangent T z).Nontrivial)
      (hLee : LeeEmbeddedCodomainRestrictionTheorem)
      (hGen : letI := A.charts
        letI := A.complexManifold
        GloballyGenerated 𝓘(ℂ,ComplexTwistorModel m)
          (contactLineCore R.tangent R.connection CR.line))
      (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
      (hAmple : letI := A.charts
        letI := A.complexManifold
        AmpleCore 𝓘(ℂ,ComplexTwistorModel m)
          (contactLineCore R.tangent R.connection CR.line)),
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
  intro R hR A B CR CP hFixed hComplex hNontrivial hLee
    hGen hFinite hAmple
  obtain ⟨zR,hzR,hRange,hQ,hTot⟩ := higher_component_restriction_geometry
    P hR3 hBG T z hz μ hchar m hm C₀ R hR
  letI : CompactSpace (FixedComponent P.tangent
      (T.connectedKernelImage P.tangent μ) z.1) := ⟨R.compact⟩
  letI : PreconnectedSpace (FixedComponent P.tangent
      (T.connectedKernelImage P.tangent μ) z.1) := ⟨R.connected⟩
  letI : Nonempty (FixedComponent P.tangent
      (T.connectedKernelImage P.tangent μ) z.1) := ⟨zR.1⟩
  have hsections := exists_torus_literal_ambient_sections_ge_two
    P R (Subtype.val : FixedComponent P.tangent
      (T.connectedKernelImage P.tangent μ) z.1 → M)
    C₀.inclusion_smooth C₀.inclusion_injective_derivative hR
    Subtype.val_injective T μ zR hRange hQ hTot A B CR CP
    hFixed hComplex (by simpa only [hzR] using hz)
    (by simpa only [hzR] using hNontrivial)
    hLee hGen hFinite hAmple
  exact ⟨zR,hzR,hsections⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicHigherComponentSectionBound
