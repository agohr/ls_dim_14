import QuaternionicSymmetry.ManifoldQuaternionicTorusAmbientSectionBoundFromSources
import QuaternionicSymmetry.ConnectedChartedSpaceDimension

/-! A nontrivial actual full-torus fixed component has at least two
sections of the literal ambient contact restriction. Connectedness and
the constructed chart atlas rule out complex dimension zero internally.
Generation and ampleness still concern the smaller intrinsic contact line;
neither ambient generation nor extremal restriction is presumed. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicTorusStrictSectionBound

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicTorusFixedComplexComponent ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorLiftedFixedSet ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldRiemannianFixedComponentGenericInput ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore ManifoldTwistorLineCoreClasses
open HolomorphicLineCoreClasses HolomorphicLineCorePullback HolomorphicLineCoreAmpleFiniteMap
open GeneralSmoothMapSource ManifoldQuaternionicTorusAmbientSectionBoundFromSources
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
  (μ : Fin r → ℤ) (z : SphereBundleTotal R.tangent)
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
theorem exists_torus_literal_ambient_sections_ge_two {m n : ℕ}
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
        a = 2 * b ∧ 0 < b ∧
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
  obtain ⟨a,H,b,C,hab,hBound⟩ := exists_torus_literal_ambient_sections_two
    P R ι hSmooth hι hR hInj T μ z hRange hQ
    hTot A B CR CP hFixed hComplex hz hNontrivial hLee hGen hFinite hAmple
  letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
    (Y P R ι hι hR T z) := C.charts
  letI : PreconnectedSpace (Y P R ι hι hR T z) :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  letI : Nontrivial (Y P R ι hι hR T z) := hNontrivial.coe_sort
  have hb := ConnectedChartedSpaceDimension.complex_dimension_pos
    (X := Y P R ι hι hR T z) b
  refine ⟨a,H,b,C,hab,hb,?_⟩
  exact hBound

end
end QuaternionicSymmetry.ManifoldQuaternionicTorusStrictSectionBound
