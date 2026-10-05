import QuaternionicSymmetry.ManifoldQuaternionicTorusAmbientSectionBound

/-! The real and complex atlases of the actual full-torus fixed component
are produced by compact-action averaging and the complex-tangent criterion, then used
in the literal ambient-contact-line section estimate. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTorusAmbientSectionBoundFromSources

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldRiemannianFixedComponentGenericInput
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap
open QuaternionicSymmetry.GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [T2Space N] [SecondCountableTopology N] [Nonempty N]
  [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  [CompactSpace M] [CompactSpace N] [PreconnectedSpace N]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : CompactConnectedPositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι)
  (hInj : Function.Injective ι)
  {r : ℕ} (T : ContinuousTorusAction P.tangent r)
  (μ : Fin r → ℤ)
  (z : SphereBundleTotal R.tangent)
  (hRange : Set.range ι = connectedComponentIn
    (ManifoldQuaternionicSpanSymmetry.fixedPoints P.tangent
      (T.connectedKernelImage P.tangent μ)) (ι z.1))
  (hQ : ∀ x ∈ Set.range ι, ∀ f ∈ T.connectedKernelImage P.tangent μ,
    ∀ a : Fin 3 → ℝ,
      ManifoldQuaternionicIsometryCoefficients.coefficientAction P.tangent f x a = a)

private abbrev c := sphereTotalMap
  P.toPositiveQuaternionicKahlerGeometry
  R.toPositiveQuaternionicKahlerGeometry ι hι hR z
private abbrev Y := ↥(component P.tangent T (c P R ι hι hR z))
private abbrev J := 𝓘(ℝ,E).prod (𝓡 2)
private abbrev V := E × EuclideanSpace ℝ (Fin 2)

include hSmooth hInj hRange hQ in
/-- The compact-action fixed-component and complex-tangent criteria
construct the atlases used for the literal ambient contact restriction.
The only line-generation and ampleness premises concern the smaller
intrinsic contact line. -/
theorem exists_torus_literal_ambient_sections_lower_bound {m n : ℕ}
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι P.connection R.connection)
    (A : CompatibleComplexAtlas R.tangent R.connection m)
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (CR : HolomorphicContactData R.tangent R.connection m A)
    (CP : HolomorphicContactData P.tangent P.connection n B)
    (hFixed : ManifoldQuaternionicTwistorFixedFromCompactAction.LiftedFixedComponents P.tangent)
    (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
    (hz : ∀ t : Torus r,
      ManifoldQuaternionicTwistorIsometryAction.sphereTotalMap P.tangent
        (T.representation t) (c P R ι hι hR z) = c P R ι hι hR z)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hGen : letI := A.charts
      letI := A.complexManifold
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel m)
        (contactLineCore R.tangent R.connection CR.line))
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hLiteral : HolomorphicAnalyticSubsetFiniteSource.SeparatedCompactAnalyticSubsetFiniteTheorem.{0,0})
    (hDim : HolomorphicFiniteMapDimensionSource.FiniteHolomorphicMapDimensionTheorem.{0,0})
    (hAmple : letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel m)
        (contactLineCore R.tangent R.connection CR.line)) :
    letI := B.charts
    ∃ a : ℕ, ∃ H : FixedComponentAtlas (J (E := E))
      (liftedSet P.tangent T.imageSubgroup) (c P R ι hι hR z) a,
      ∃ b : ℕ, ∃ C : ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas P.tangent P.connection B T.imageSubgroup H) b,
        a = 2 * b ∧
        (letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
            (Y P R ι hι hR T z) := C.charts
         Module.finrank ℂ (EuclideanSpace ℂ (Fin b)) + 1 ≤ Module.finrank ℂ
           (GlobalSections 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
             (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
               𝓘(ℂ,EuclideanSpace ℂ (Fin b))
               (contactLineCore P.tangent P.connection CP.line)
               (Subtype.val : Y P R ι hι hR T z → SphereBundleTotal P.tangent)
               C.inclusion_holomorphic))) := by
  letI := B.charts
  obtain ⟨a,H,b,C,hab,_⟩ := exists_complexComponentAtlas
    P.tangent T P.connection B hFixed hComplex
    (c P R ι hι hR z) hz
  refine ⟨a,H,b,C,hab,?_⟩
  letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
    (Y P R ι hι hR T z) := C.charts
  exact ManifoldQuaternionicTorusAmbientSectionBound.torus_literal_ambient_sections_lower_bound
    P R ι hSmooth hι hR hInj T μ z hRange hQ
    hTot A B CR CP H C hz hLee hGen hFinite hLiteral hDim hAmple

include hSmooth hInj hRange hQ in
/-- The same geometric restriction has at least two sections, by the
compact-manifold argument; no compact-analytic-subset premise is used. -/
theorem exists_torus_literal_ambient_sections_two {m n : ℕ}
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι P.connection R.connection)
    (A : CompatibleComplexAtlas R.tangent R.connection m)
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (CR : HolomorphicContactData R.tangent R.connection m A)
    (CP : HolomorphicContactData P.tangent P.connection n B)
    (hFixed : ManifoldQuaternionicTwistorFixedFromCompactAction.LiftedFixedComponents P.tangent)
    (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
    (hz : ∀ t : Torus r,
      ManifoldQuaternionicTwistorIsometryAction.sphereTotalMap P.tangent
        (T.representation t) (c P R ι hι hR z) = c P R ι hι hR z)
    (hNontrivial : (component P.tangent T (c P R ι hι hR z)).Nontrivial)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hGen : letI := A.charts
      letI := A.complexManifold
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel m)
        (contactLineCore R.tangent R.connection CR.line))
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hAmple : letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel m)
        (contactLineCore R.tangent R.connection CR.line)) :
    letI := B.charts
    ∃ a : ℕ, ∃ H : FixedComponentAtlas (J (E := E))
      (liftedSet P.tangent T.imageSubgroup) (c P R ι hι hR z) a,
      ∃ b : ℕ, ∃ C : ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas P.tangent P.connection B T.imageSubgroup H) b,
        a = 2 * b ∧
        (letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
            (Y P R ι hι hR T z) := C.charts
         2 ≤ Module.finrank ℂ
           (GlobalSections 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
             (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
               𝓘(ℂ,EuclideanSpace ℂ (Fin b))
               (contactLineCore P.tangent P.connection CP.line)
               (Subtype.val : Y P R ι hι hR T z → SphereBundleTotal P.tangent)
               C.inclusion_holomorphic))) := by
  letI := B.charts
  obtain ⟨a,H,b,C,hab,_⟩ := exists_complexComponentAtlas
    P.tangent T P.connection B hFixed hComplex
    (c P R ι hι hR z) hz
  refine ⟨a,H,b,C,hab,?_⟩
  letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
    (Y P R ι hι hR T z) := C.charts
  exact ManifoldQuaternionicTorusAmbientSectionBound.torus_literal_ambient_sections_ge_two
    P R ι hSmooth hι hR hInj T μ z hRange hQ
    hTot A B CR CP H C hz hNontrivial hLee hGen hFinite hAmple


end
end QuaternionicSymmetry.ManifoldQuaternionicTorusAmbientSectionBoundFromSources
