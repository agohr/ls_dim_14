import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmpleRescaled
import QuaternionicSymmetry.HolomorphicLineCoreRestrictedFiniteEstimate
import QuaternionicSymmetry.HolomorphicLineFiniteSectionsSource

/-! The checked Demailly restricted-section estimate applied to the
genuine contact quotient line of a source-selected positive-Ricci twistor.
Ampleness is supplied separately by
`exists_rescaled_ample_contact_core`; generation is kept explicit since
ampleness alone does not imply it for the unpowered contact line. -/

namespace QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldTwistorSphereCore
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineCoreRestrictedFiniteEstimate
open HolomorphicAnalyticSubsetFiniteSource
open HolomorphicFiniteMapDimensionSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable {Y FY : Type}
  [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [CompactSpace Y] [Nonempty Y]
  [NormedAddCommGroup FY] [NormedSpace ℂ FY] [FiniteDimensional ℂ FY]
  [ChartedSpace FY Y] [IsManifold 𝓘(ℂ,FY) ∞ Y]

/-- For an actual compact holomorphic inclusion into the selected twistor,
an ample and globally generated contact line has at least dimension-plus-
one holomorphic sections after restriction. The only general analytic
premises are Demailly's literal compact-analytic-subset and finite-map
dimension theorems; the source's T1 positive Ricci gives `hAmple` through
the separately checked `exists_rescaled_ample_contact_core`. -/
theorem contact_restricted_section_finrank_bound_literal
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    {n : ℕ} (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A) :
    letI := A.charts
    letI := A.complexManifold
    ∀
    (f : Y → SphereBundleTotal P.tangent)
    (hf : ContMDiff 𝓘(ℂ,FY) 𝓘(ℂ,ComplexTwistorModel n) ∞ f)
    (d : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line)))
    (hGen : GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line))
    (e : ℕ)
    (c : Module.Basis (Fin (e + 1)) ℂ
      (GlobalSections 𝓘(ℂ,FY)
        (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,FY)
          (contactLineCore P.tangent P.connection C.contact.line) f hf)))
    (hLiteral : SeparatedCompactAnalyticSubsetFiniteTheorem.{0,0})
    (hDim : FiniteHolomorphicMapDimensionTheorem.{0,0})
    (hAmple : AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line))
    (hfInj : Function.Injective f),
    Module.finrank ℂ FY + 1 ≤
      Module.finrank ℂ
        (GlobalSections 𝓘(ℂ,FY)
          (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,FY)
            (contactLineCore P.tangent P.connection C.contact.line) f hf)) := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  intro f hf d b hGen e c hLiteral hDim hAmple hfInj
  exact restricted_section_finrank_bound_literal
    (contactLineCore P.tangent P.connection C.contact.line)
    f hf d b hGen e c hLiteral hDim hAmple hfInj

/-- The same actual twistor estimate without assumed finite bases. The
general compact-section finiteness theorem and genuine generation produce
both bases internally, including nonzero sections on the restriction. -/
theorem contact_restricted_section_finrank_bound_from_finiteness
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    {n : ℕ} (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A) :
    letI := A.charts
    letI := A.complexManifold
    ∀ (f : Y → SphereBundleTotal P.tangent)
      (hf : ContMDiff 𝓘(ℂ,FY) 𝓘(ℂ,ComplexTwistorModel n) ∞ f)
      (hGen : GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
      (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
      (hLiteral : SeparatedCompactAnalyticSubsetFiniteTheorem.{0,0})
      (hDim : FiniteHolomorphicMapDimensionTheorem.{0,0})
      (hAmple : AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
      (hfInj : Function.Injective f),
      Module.finrank ℂ FY + 1 ≤ Module.finrank ℂ
        (GlobalSections 𝓘(ℂ,FY)
          (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,FY)
            (contactLineCore P.tangent P.connection C.contact.line) f hf)) := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  intro f hf hGen hFinite hLiteral hDim hAmple hfInj
  exact HolomorphicLineFiniteSectionsSource.restricted_section_finrank_bound_from_finiteness
    hFinite (contactLineCore P.tangent P.connection C.contact.line)
    f hf hGen hLiteral hDim hAmple hfInj

end
end QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple
