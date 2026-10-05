import QuaternionicSymmetry.ManifoldQuaternionicTorusToIntrinsicHolomorphic
import QuaternionicSymmetry.ManifoldQuaternionicInducedContactArbitraryRestriction

/-! Actual full-torus fixed-component section estimate, transported through
the connected kernel component to the intrinsic smaller twistor. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTorusContactRestriction

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicTorusToIntrinsicHolomorphic
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
private abbrev Y := ManifoldQuaternionicTorusFixedComplexComponent.component
  P.tangent T (c P R ι hι hR z)

local instance : Fact (Module.finrank ℝ ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) :=
  ⟨by simp⟩
local instance (x : N) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore R.tangent).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

include hSmooth hInj hRange hQ in
/-- The ambient contact line restricted to the actual full-torus fixed
component has at least its complex dimension plus one global sections.
Generation and ampleness are requested only of the intrinsic smaller line. -/
theorem torus_restricted_ambient_sections_lower_bound {a b m n : ℕ}
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
    letI := A.charts
    letI := B.charts
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
      (Y P R ι hι hR T z) := C.charts
    letI := ManifoldQuaternionicFixedComponentComplexAtlas.charts
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A
    letI := A.complexManifold
    letI := B.complexManifold
    letI := ManifoldQuaternionicFixedComponentComplexAtlas.complexManifold
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A
    let j := (ManifoldQuaternionicFixedComponentComplexAtlas.biholomorph
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A).symm ∘
      inclusionIntoConnectedKernelComponent P.tangent T μ
        (c P R ι hι hR z)
    let hj := (torusToIntrinsic_holomorphic_injective
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
      T μ z hRange hQ P.connection R.connection hTot A B H C hLee).1
    Module.finrank ℂ (EuclideanSpace ℂ (Fin b)) + 1 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel m)
          𝓘(ℂ,EuclideanSpace ℂ (Fin b))
          (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
            𝓘(ℂ,ComplexTwistorModel m)
            (contactLineCore P.tangent P.connection CP.line)
            (sphereTotalMap P.toPositiveQuaternionicKahlerGeometry
              R.toPositiveQuaternionicKahlerGeometry ι hι hR)
            (ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
              P.toPositiveQuaternionicKahlerGeometry
              R.toPositiveQuaternionicKahlerGeometry ι hSmooth hι hR
              P.connection R.connection hTot A B)) j hj)) := by
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
  have hfixed := (mem_fixedSpherePoints_iff_torus P.tangent T
    (c P R ι hι hR z)).mpr hz
  letI : CompactSpace (Y P R ι hι hR T z) :=
    compactComponent P.tangent T (c P R ι hι hR z) hfixed
  letI : Nonempty (Y P R ι hι hR T z) :=
    nonemptyComponent P.tangent T (c P R ι hι hR z) hfixed
  let j := (ManifoldQuaternionicFixedComponentComplexAtlas.biholomorph
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A).symm ∘
    inclusionIntoConnectedKernelComponent P.tangent T μ
      (c P R ι hι hR z)
  obtain ⟨hj,hjInj⟩ := torusToIntrinsic_holomorphic_injective
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
    T μ z hRange hQ P.connection R.connection hTot A B H C hLee
  exact ManifoldQuaternionicInducedContactArbitraryRestriction.ambient_restriction_sections_lower_bound
    P R ι hSmooth hι hR hTot A B CR CP j hj hjInj
    hGen hFinite hLiteral hDim hAmple

include hSmooth hInj hRange hQ in
/-- The same geometric restriction has at least two sections, by the
compact-manifold argument; no compact-analytic-subset premise is used. -/
theorem torus_restricted_ambient_sections_ge_two {a b m n : ℕ}
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
    letI := A.charts
    letI := B.charts
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
      (Y P R ι hι hR T z) := C.charts
    letI := ManifoldQuaternionicFixedComponentComplexAtlas.charts
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A
    letI := A.complexManifold
    letI := B.complexManifold
    letI := ManifoldQuaternionicFixedComponentComplexAtlas.complexManifold
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A
    let j := (ManifoldQuaternionicFixedComponentComplexAtlas.biholomorph
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A).symm ∘
      inclusionIntoConnectedKernelComponent P.tangent T μ
        (c P R ι hι hR z)
    let hj := (torusToIntrinsic_holomorphic_injective
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
      T μ z hRange hQ P.connection R.connection hTot A B H C hLee).1
    2 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel m)
          𝓘(ℂ,EuclideanSpace ℂ (Fin b))
          (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
            𝓘(ℂ,ComplexTwistorModel m)
            (contactLineCore P.tangent P.connection CP.line)
            (sphereTotalMap P.toPositiveQuaternionicKahlerGeometry
              R.toPositiveQuaternionicKahlerGeometry ι hι hR)
            (ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
              P.toPositiveQuaternionicKahlerGeometry
              R.toPositiveQuaternionicKahlerGeometry ι hSmooth hι hR
              P.connection R.connection hTot A B)) j hj)) := by
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
  have hfixed := (mem_fixedSpherePoints_iff_torus P.tangent T
    (c P R ι hι hR z)).mpr hz
  letI : CompactSpace (Y P R ι hι hR T z) :=
    compactComponent P.tangent T (c P R ι hι hR z) hfixed
  letI : Nonempty (Y P R ι hι hR T z) :=
    nonemptyComponent P.tangent T (c P R ι hι hR z) hfixed
  let j := (ManifoldQuaternionicFixedComponentComplexAtlas.biholomorph
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ R.connection A).symm ∘
    inclusionIntoConnectedKernelComponent P.tangent T μ
      (c P R ι hι hR z)
  obtain ⟨hj,hjInj⟩ := torusToIntrinsic_holomorphic_injective
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR hSmooth hInj
    T μ z hRange hQ P.connection R.connection hTot A B H C hLee
  exact ManifoldQuaternionicInducedContactArbitraryRestriction.ambient_restriction_sections_ge_two
    P R ι hSmooth hι hR hTot A B CR CP j hj hjInj
    hGen hFinite hAmple


end
end QuaternionicSymmetry.ManifoldQuaternionicTorusContactRestriction
