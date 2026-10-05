import QuaternionicSymmetry.ManifoldQuaternionicTorusAmbientRestriction

/-! The final full-torus section estimate is stated on the literal ambient
contact line restricted along the actual ambient subtype inclusion. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTorusAmbientSectionBound

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
open ManifoldQuaternionicTorusContactRestriction
open ManifoldQuaternionicTorusAmbientRestriction
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

include hSmooth hInj hRange hQ in
/-- The literal ambient contact line `L_M|_Y`, not merely a nested
representation of it, has at least `dim_C Y + 1` global sections. -/
theorem torus_literal_ambient_sections_lower_bound {a b m n : ℕ}
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι P.connection R.connection)
    (A : CompatibleComplexAtlas R.tangent R.connection m)
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (CR : HolomorphicContactData R.tangent R.connection m A)
    (CP : HolomorphicContactData P.tangent P.connection n B)
    (H : FixedComponentAtlas (𝓘(ℝ,E).prod (𝓡 2))
      (liftedSet P.tangent T.imageSubgroup)
      (c P R ι hι hR z) a)
    (C : letI := B.charts
      ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas P.tangent P.connection B T.imageSubgroup H) b)
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
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
      (Y P R ι hι hR T z) := C.charts
    letI := B.complexManifold
    Module.finrank ℂ (EuclideanSpace ℂ (Fin b)) + 1 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
          𝓘(ℂ,EuclideanSpace ℂ (Fin b))
          (contactLineCore P.tangent P.connection CP.line)
          (Subtype.val : Y P R ι hι hR T z → SphereBundleTotal P.tangent)
          C.inclusion_holomorphic)) := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
    (Y P R ι hι hR T z) := C.charts
  letI : IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞
    (Y P R ι hι hR T z) := C.manifold
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.charts
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.complexManifold
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A
  have hBound := torus_restricted_ambient_sections_lower_bound
    P R ι hSmooth hι hR hInj T μ z hRange hQ
    hTot A B CR CP H C hz hLee hGen hFinite hLiteral hDim hAmple
  have hLine := torus_iteratedLine_eq_ambientRestriction
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
    T μ z hRange hQ P.connection R.connection hTot A B H C hLee
    (contactLineCore P.tangent P.connection CP.line)
  exact hLine ▸ hBound

include hSmooth hInj hRange hQ in
/-- The same geometric restriction has at least two sections, by the
compact-manifold argument; no compact-analytic-subset premise is used. -/
theorem torus_literal_ambient_sections_ge_two {a b m n : ℕ}
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι P.connection R.connection)
    (A : CompatibleComplexAtlas R.tangent R.connection m)
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (CR : HolomorphicContactData R.tangent R.connection m A)
    (CP : HolomorphicContactData P.tangent P.connection n B)
    (H : FixedComponentAtlas (𝓘(ℝ,E).prod (𝓡 2))
      (liftedSet P.tangent T.imageSubgroup)
      (c P R ι hι hR z) a)
    (C : letI := B.charts
      ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas P.tangent P.connection B T.imageSubgroup H) b)
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
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
      (Y P R ι hι hR T z) := C.charts
    letI := B.complexManifold
    2 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
          𝓘(ℂ,EuclideanSpace ℂ (Fin b))
          (contactLineCore P.tangent P.connection CP.line)
          (Subtype.val : Y P R ι hι hR T z → SphereBundleTotal P.tangent)
          C.inclusion_holomorphic)) := by
  letI : PreconnectedSpace (Y P R ι hι hR T z) :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  letI : Nontrivial (Y P R ι hι hR T z) := hNontrivial.coe_sort
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
    (Y P R ι hι hR T z) := C.charts
  letI : IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞
    (Y P R ι hι hR T z) := C.manifold
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.charts
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.complexManifold
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A
  have hBound := torus_restricted_ambient_sections_ge_two
    P R ι hSmooth hι hR hInj T μ z hRange hQ
    hTot A B CR CP H C hz hNontrivial hLee hGen hFinite hAmple
  have hLine := torus_iteratedLine_eq_ambientRestriction
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
    T μ z hRange hQ P.connection R.connection hTot A B H C hLee
    (contactLineCore P.tangent P.connection CP.line)
  exact hLine ▸ hBound


end
end QuaternionicSymmetry.ManifoldQuaternionicTorusAmbientSectionBound
