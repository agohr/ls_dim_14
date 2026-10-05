import QuaternionicSymmetry.HolomorphicLineCoreRestrictedFiniteEstimate

/-! Published background: Wells, *Differential Analysis on Complex Manifolds*,
3rd ed., Springer GTM 65, IV §5 Theorem 5.2(c), p.147, and Example 5.7,
pp.151–152, give finite-dimensional cohomology for holomorphic bundles
on compact complex manifolds. Degree zero is actual global sections.
See Textbooks/STAGE2_FIDELITY_REVIEW_20261001.md for provenance. -/

namespace QuaternionicSymmetry.HolomorphicLineFiniteSectionsSource

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreRestrictedFiniteEstimate
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicAnalyticSubsetFiniteSource HolomorphicFiniteMapDimensionSource
open scoped Manifold ContDiff
noncomputable section

/-- The general rank-one compact-section corollary of Cartan–Serre. There
is no Fano, contact, generation, positivity or numerical bound conclusion. -/
def CompactHolomorphicLineSectionFiniteness : Prop :=
  ∀ {B F : Type} [TopologicalSpace B] [T2Space B]
    [SecondCountableTopology B] [CompactSpace B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
    (L : LineCore.{0} (B := B) 𝓘(ℂ,F)),
      FiniteDimensional ℂ (GlobalSections 𝓘(ℂ,F) L)

variable {B F : Type} [TopologicalSpace B] [T2Space B]
  [SecondCountableTopology B] [CompactSpace B] [Nonempty B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]

/-- Global generation provides a nonzero genuine section. The general
finiteness source therefore yields a finite basis with nonempty index set,
without assuming either such a basis or a prescribed section count. -/
theorem exists_nonempty_section_basis
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (L : LineCore.{0} (B := B) 𝓘(ℂ,F))
    (hGen : GloballyGenerated 𝓘(ℂ,F) L) :
    ∃ d : ℕ, Nonempty (Module.Basis (Fin (d + 1)) ℂ
      (GlobalSections 𝓘(ℂ,F) L)) := by
  letI := hFinite L
  obtain ⟨x⟩ := ‹Nonempty B›
  obtain ⟨s, hs⟩ := hGen x
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    simpa only [h] using (show (0 : GlobalSections 𝓘(ℂ,F) L) x = 0 from rfl)
  have hpos : 0 < Module.finrank ℂ (GlobalSections 𝓘(ℂ,F) L) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨s, hs0⟩
  let d := Module.finrank ℂ (GlobalSections 𝓘(ℂ,F) L) - 1
  have hd : Module.finrank ℂ (GlobalSections 𝓘(ℂ,F) L) = d + 1 := by
    dsimp [d]
    omega
  exact ⟨d, ⟨(Module.finBasis ℂ (GlobalSections 𝓘(ℂ,F) L)).reindex (finCongr hd)⟩⟩

variable {B' F' : Type} [TopologicalSpace B'] [T2Space B']
  [SecondCountableTopology B'] [CompactSpace B'] [Nonempty B']
  [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  [ChartedSpace F' B'] [IsManifold 𝓘(ℂ,F') ∞ B']

/-- The actual restricted-section bound no longer assumes finite bases:
they follow from general compact-section finiteness and actual generation.
All remaining source premises are general analytic theorems. -/
theorem restricted_section_finrank_bound_from_finiteness
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (L : LineCore.{0} (B := B) 𝓘(ℂ,F))
    (f : B' → B) (hf : ContMDiff 𝓘(ℂ,F') 𝓘(ℂ,F) ∞ f)
    (hGen : GloballyGenerated 𝓘(ℂ,F) L)
    (hLiteral : SeparatedCompactAnalyticSubsetFiniteTheorem.{0,0})
    (hDim : FiniteHolomorphicMapDimensionTheorem.{0,0})
    (hAmple : AmpleCore 𝓘(ℂ,F) L) (hfInj : Function.Injective f) :
    Module.finrank ℂ F' + 1 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,F') (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf)) := by
  obtain ⟨d, ⟨b⟩⟩ := exists_nonempty_section_basis hFinite L hGen
  obtain ⟨e, ⟨c⟩⟩ := exists_nonempty_section_basis hFinite
    (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf)
    (globallyGenerated_pullback 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf hGen)
  exact restricted_section_finrank_bound_literal L f hf d b hGen e c hLiteral hDim hAmple hfInj

end
end QuaternionicSymmetry.HolomorphicLineFiniteSectionsSource
