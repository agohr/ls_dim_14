import QuaternionicSymmetry.ManifoldSWKillingVolumeBound
import QuaternionicSymmetry.ManifoldSWEquation22SourceContract
import QuaternionicSymmetry.ManifoldTwistorSWSourceContract
import QuaternionicSymmetry.ManifoldTwistorLeBrunExistenceInput
import QuaternionicSymmetry.ManifoldQuaternionicKillingHomothety
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.SheafComplexSheafification

/-! Source-facing quantitative Killing-field bounds. The actual-volume
statement takes compatible twistor contact data; the existence statement
constructs them on a normalized homothety and records that volume explicitly.
No homothety invariance of the analytic integral is assumed. -/
namespace QuaternionicSymmetry.ManifoldSWKillingVolumeFromSources
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldSWKillingVolumeBound
open ManifoldPositiveQuaternionicKahlerQuantitativeBounds
open ManifoldSWActualHilbertValues
open ManifoldPositiveQuaternionicKahlerAllVirtualBounds
open ManifoldSWEquation22SourceContract
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicKillingHomothety ManifoldQuaternionicMetric
open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [T2Space M] [SecondCountableTopology M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

/-- The full chain in the main paper's lower-bound corollary, for actual
compatible contact data. All geometric and index inputs are exactly the
existing registered source contracts. -/
theorem killing_dimension_volume_bounds_from_sources
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection
      S.quaternionicDimension A)
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 14) :
    (delta S.quaternionicDimension : ℝ) +
        (scalarCoefficient S.quaternionicDimension : ℝ) * quaternionicVolume S P ≤
        (ManifoldQuaternionicKillingFields.killingDimension P.tangent : ℝ) ∧
      (delta S.quaternionicDimension : ℝ) <
        (delta S.quaternionicDimension : ℝ) +
          (scalarCoefficient S.quaternionicDimension : ℝ) * quaternionicVolume S P ∧
      4 ≤ delta S.quaternionicDimension := by
  letI : HasSheafify (Opens.grothendieckTopology
      (TopCat.of (SphereBundleTotal P.tangent))) (ModuleCat.{0} ℂ) :=
    SheafComplexSheafification.topCatHasSheafify
      (TopCat.of (SphereBundleTotal P.tangent))
  letI : HasExt.{1} (TopCat.Sheaf (ModuleCat.{0} ℂ)
      (TopCat.of (SphereBundleTotal P.tangent))) := HasExt.standard _
  have hCanonical := contactCanonicalIso_of_generalContact
    P.tangent P.connection hGeneral C
  rcases swCohomology_of_generalContact P C hCohom hGeneral hn.1 S.real_finrank with
    ⟨hfinite, hKodairaPositive, hKodairaNegative, hSerre, ⟨hSalamon⟩⟩
  refine ⟨killing_dimension_volume_lower_bound S P hsource hAmann hsp heq38
    A C (hEquation S P A C) hn hCanonical (Classical.choice inferInstance) hfinite
    (hKodairaPositive 0 (by omega)) (hKodairaPositive 1 (by omega))
    hKodairaNegative hSerre hSalamon,
    offset_lt_volume_lower_bound S P hsp heq38 hn.1, ?_⟩
  unfold delta
  split_ifs with heven <;> omega

/-- Normalized existence needs no supplied contact geometry. The volume is
explicitly that of the produced homothety; Killing dimension is transported
back to the original metric by the existing checked equivalence. -/
theorem exists_normalized_killing_dimension_volume_bounds
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedComplexContactExistence.{0,0})
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 14) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      0 < quaternionicVolume S (rescaleCompact P s hs) ∧
      (delta S.quaternionicDimension : ℝ) +
        (scalarCoefficient S.quaternionicDimension : ℝ) *
          quaternionicVolume S (rescaleCompact P s hs) ≤
        (ManifoldQuaternionicKillingFields.killingDimension P.tangent : ℝ) := by
  obtain ⟨s, hs, A, _, C, _⟩ :=
    exists_normalized_contact_canonical hT1 hGeneral S P heq38 hn.1
  have hb := (killing_dimension_volume_bounds_from_sources S (rescaleCompact P s hs)
    hsource hAmann hsp heq38 hGeneral hEquation hCohom A C hn).1
  rw [killingDimension_rescaleCompact P s hs] at hb
  exact ⟨s, hs, quaternionicVolume_pos S (rescaleCompact P s hs) hsp heq38 hn.1, hb⟩

end
end QuaternionicSymmetry.ManifoldSWKillingVolumeFromSources
