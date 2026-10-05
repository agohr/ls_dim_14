import QuaternionicSymmetry.HolomorphicLineTwoSections
import QuaternionicSymmetry.ManifoldQuaternionicInducedContactSubrestriction

/-! The actual induced-contact section bound for any compact complex source
holomorphically and injectively mapped into the intrinsic smaller twistor.
This permits the genuine full-torus component, which need not be a subtype
of the smaller twistor or equal to its entire space. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicInducedContactArbitraryRestriction

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedContactLinePullback
open ManifoldQuaternionicInducedContactGaugeWitness
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineGaugePullbackSections
open scoped Manifold ContDiff
noncomputable section

variable {E F G M N Y : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [FiniteDimensional ℂ G]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [T2Space N] [SecondCountableTopology N] [Nonempty N]
  [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [CompactSpace Y] [Nonempty Y]
  [ChartedSpace G Y] [IsManifold 𝓘(ℂ,G) ∞ Y]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : CompactConnectedPositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι)
  (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
    P.toPositiveQuaternionicKahlerGeometry R.toPositiveQuaternionicKahlerGeometry
    ι P.connection R.connection)

local instance : Fact (Module.finrank ℝ ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) :=
  ⟨by simp⟩
local instance (x : N) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore R.tangent).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

include hSmooth hι hR hTot in
/-- The bound is imposed on the literal source `Y`; no ambient-line
generation, and no equality `Y = Z(N)`, is assumed. -/
theorem ambient_restriction_sections_lower_bound {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent R.connection m)
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (CR : HolomorphicContactData R.tangent R.connection m A)
    (CP : HolomorphicContactData P.tangent P.connection n B)
    (j : Y → SphereBundleTotal R.tangent)
    (hj : letI := A.charts
      letI := A.complexManifold
      ContMDiff 𝓘(ℂ,G) 𝓘(ℂ,ComplexTwistorModel m) ∞ j)
    (hjInj : Function.Injective j)
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
    letI := A.complexManifold
    letI := B.complexManifold
    Module.finrank ℂ G + 1 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,G)
        (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel m) 𝓘(ℂ,G)
          (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
            𝓘(ℂ,ComplexTwistorModel m)
            (contactLineCore P.tangent P.connection CP.line)
            (sphereTotalMap P.toPositiveQuaternionicKahlerGeometry
              R.toPositiveQuaternionicKahlerGeometry ι hι hR)
            (ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
              P.toPositiveQuaternionicKahlerGeometry
              R.toPositiveQuaternionicKahlerGeometry ι hSmooth hι hR
              P.connection R.connection hTot A B))
          j hj)) := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  letI : CompactSpace N := ⟨R.compact⟩
  let Φ := sphereTotalMap P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR
  let hΦ := ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hSmooth hι hR
    P.connection R.connection hTot A B
  let LN := contactLineCore R.tangent R.connection CR.line
  let LM := contactLineCore P.tangent P.connection CP.line
  have hBound :=
    HolomorphicLineFiniteSectionsSource.restricted_section_finrank_bound_from_finiteness
      hFinite LN j hj hGen hLiteral hDim hAmple hjInj
  have hGauge := actual_hasLocalHolomorphicWitness
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hSmooth hι hR
    P.connection R.connection hTot A B CR CP
  let e := restrictedContactLineFiberEquiv
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hSmooth hι hR
    P.connection R.connection hTot A B CR.line CP.line
  have hEquiv := pullbackSectionLinearEquiv
    𝓘(ℂ,ComplexTwistorModel m) 𝓘(ℂ,G) LN
    (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel m) LM Φ hΦ)
    j hj e hGauge
  simpa [LN, LM, Φ, hΦ, contactLineCore,
    ManifoldQuaternionicInducedContactLinePullback.restrictedAmbientCore]
    using hBound.trans_eq hEquiv.finrank_eq

include hSmooth hι hR hTot in
/-- The same geometric restriction has at least two sections, by the
compact-manifold argument; no compact-analytic-subset premise is used. -/
theorem ambient_restriction_sections_ge_two [PreconnectedSpace Y] [Nontrivial Y] {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent R.connection m)
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (CR : HolomorphicContactData R.tangent R.connection m A)
    (CP : HolomorphicContactData P.tangent P.connection n B)
    (j : Y → SphereBundleTotal R.tangent)
    (hj : letI := A.charts
      letI := A.complexManifold
      ContMDiff 𝓘(ℂ,G) 𝓘(ℂ,ComplexTwistorModel m) ∞ j)
    (hjInj : Function.Injective j)
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
    letI := A.complexManifold
    letI := B.complexManifold
    2 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,G)
        (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel m) 𝓘(ℂ,G)
          (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
            𝓘(ℂ,ComplexTwistorModel m)
            (contactLineCore P.tangent P.connection CP.line)
            (sphereTotalMap P.toPositiveQuaternionicKahlerGeometry
              R.toPositiveQuaternionicKahlerGeometry ι hι hR)
            (ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
              P.toPositiveQuaternionicKahlerGeometry
              R.toPositiveQuaternionicKahlerGeometry ι hSmooth hι hR
              P.connection R.connection hTot A B))
          j hj)) := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  letI : CompactSpace N := ⟨R.compact⟩
  let Φ := sphereTotalMap P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR
  let hΦ := ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hSmooth hι hR
    P.connection R.connection hTot A B
  let LN := contactLineCore R.tangent R.connection CR.line
  let LM := contactLineCore P.tangent P.connection CP.line
  have hBound :=
    HolomorphicLineTwoSections.restricted_sections_ge_two_of_ample
      hFinite LN j hj hGen hAmple hjInj
  have hGauge := actual_hasLocalHolomorphicWitness
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hSmooth hι hR
    P.connection R.connection hTot A B CR CP
  let e := restrictedContactLineFiberEquiv
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hSmooth hι hR
    P.connection R.connection hTot A B CR.line CP.line
  have hEquiv := pullbackSectionLinearEquiv
    𝓘(ℂ,ComplexTwistorModel m) 𝓘(ℂ,G) LN
    (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel m) LM Φ hΦ)
    j hj e hGauge
  simpa [LN, LM, Φ, hΦ, contactLineCore,
    ManifoldQuaternionicInducedContactLinePullback.restrictedAmbientCore]
    using hBound.trans_eq hEquiv.finrank_eq


end
end QuaternionicSymmetry.ManifoldQuaternionicInducedContactArbitraryRestriction
