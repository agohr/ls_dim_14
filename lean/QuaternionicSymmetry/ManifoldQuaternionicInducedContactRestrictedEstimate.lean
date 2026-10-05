import QuaternionicSymmetry.ManifoldQuaternionicInducedContactSections
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.HolomorphicLineFiniteSectionsSource

/-! Transfer the existing ample generated *ambient-restriction* estimate to
the actual intrinsic contact-line section space using the constructed
holomorphic line gauge. The line identification is no longer a premise. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedContactRestrictedEstimate
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedContactLinePullback
open ManifoldQuaternionicInducedContactSections
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCoreClasses
open HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap
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
variable (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
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
/-- The Demailly restricted-section lower bound, now on the *intrinsic*
contact line of the induced positive quaternionic-Kähler geometry. -/
theorem intrinsic_contact_sections_lower_bound {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent R.connection m)
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (CR : HolomorphicContactData R.tangent R.connection m A)
    (CP : HolomorphicContactData P.tangent P.connection n B)
    (hBaseInj : Function.Injective ι) :
    letI := A.charts
    letI := B.charts
    letI := A.complexManifold
    letI := B.complexManifold
    ∀ (hGen : GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection CP.line))
      (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
      (hLiteral : HolomorphicAnalyticSubsetFiniteSource.SeparatedCompactAnalyticSubsetFiniteTheorem.{0,0})
      (hDim : HolomorphicFiniteMapDimensionSource.FiniteHolomorphicMapDimensionTheorem.{0,0})
      (hAmple : AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection CP.line)),
    Module.finrank ℂ (ComplexTwistorModel m) + 1 ≤
      Module.finrank ℂ
        (GlobalSections 𝓘(ℂ,ComplexTwistorModel m)
          (contactLineCore R.tangent R.connection CR.line)) := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  intro hGen hFinite hLiteral hDim hAmple
  letI : CompactSpace M := ⟨P.compact⟩
  letI : CompactSpace N := ⟨R.compact⟩
  let Φ := sphereTotalMap P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry ι hι hR
  have hΦ : ContMDiff 𝓘(ℂ,ComplexTwistorModel m)
      𝓘(ℂ,ComplexTwistorModel n) ∞ Φ :=
    ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
      P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry
      ι hSmooth hι hR P.connection R.connection hTot A B
  have hΦInj : Function.Injective Φ :=
    sphereTotalMap_injective P.toPositiveQuaternionicKahlerGeometry
      R.toPositiveQuaternionicKahlerGeometry ι hι hR hBaseInj
  have hBound :=
    HolomorphicLineFiniteSectionsSource.restricted_section_finrank_bound_from_finiteness
      hFinite (contactLineCore P.tangent P.connection CP.line)
      Φ hΦ hGen hLiteral hDim hAmple hΦInj
  have hSections := actualInducedContactSectionLinearEquiv
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry
    ι hSmooth hι hR P.connection R.connection hTot A B CR CP
  simpa [contactLineCore, HolomorphicLineCorePullback.pullbackLineCore,
    ManifoldQuaternionicInducedContactLinePullback.restrictedAmbientCore]
    using hBound.trans_eq hSections.finrank_eq.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedContactRestrictedEstimate
