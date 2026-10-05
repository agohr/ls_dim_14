import QuaternionicSymmetry.ManifoldSWKillingDimensionBound
import QuaternionicSymmetry.ManifoldSWEquation22SourceContract
import QuaternionicSymmetry.ManifoldTwistorSWSourceContract
import QuaternionicSymmetry.ManifoldTwistorLeBrunExistenceInput
import QuaternionicSymmetry.ManifoldQuaternionicKillingHomothety
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.SheafComplexSheafification

/-! The source-facing finite-dimensional symmetry bound on the original
actual positive quaternionic-Kähler metric. LeBrun's contact data live on
a normalized homothety; equality of the genuine Killing-field spaces
transfers the bound back. Sheafification and Ext are constructed from
Mathlib's categorical infrastructure at fixed small universes. -/
namespace QuaternionicSymmetry.ManifoldSWNormalizedKillingBound
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldSWKillingDimensionBound
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

theorem killing_dimension_lower_bound_from_sources
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedComplexContactExistence.{0,0})
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 14) :
    QuaternionicSymmetry.delta S.quaternionicDimension + 1 ≤
      ManifoldQuaternionicKillingFields.killingDimension P.tangent := by
  obtain ⟨s, hs, A, _, C, hCanonical⟩ :=
    exists_normalized_contact_canonical hT1 hGeneral S P heq38 hn.1
  let R := rescaleCompact P s hs
  letI : HasSheafify (Opens.grothendieckTopology
      (TopCat.of (SphereBundleTotal R.tangent))) (ModuleCat.{0} ℂ) :=
    SheafComplexSheafification.topCatHasSheafify
      (TopCat.of (SphereBundleTotal R.tangent))
  letI : HasExt.{1} (TopCat.Sheaf (ModuleCat.{0} ℂ)
      (TopCat.of (SphereBundleTotal R.tangent))) :=
    HasExt.standard _
  have hSW := hEquation S R A C
  have hH := swCohomology_of_generalContact R C hCohom hGeneral
    hn.1 S.real_finrank
  rcases hH with ⟨hfinite, hKodairaPositive, hKodairaNegative, hSerre,
    ⟨hSalamon⟩⟩
  have hsections : QuaternionicSymmetry.delta S.quaternionicDimension + 1 ≤
      ManifoldQuaternionicKillingFields.killingDimension R.tangent := by
    exact killing_dimension_lower_bound S R hsource hAmann hsp heq38
      A C hSW hn hCanonical (Classical.choice inferInstance) hfinite
      (hKodairaPositive 0 (by omega))
      (hKodairaPositive 1 (by omega)) hKodairaNegative hSerre hSalamon
  simpa only [R, killingDimension_rescaleCompact P s hs] using hsections

/-- The C12 range uses only the source scalar and orbital formulas; Amann's
intersection-form theorem enters the separate dimensions 13 and 14 branch. -/
theorem killing_dimension_lower_bound_c12_from_sources
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedComplexContactExistence.{0,0})
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 12) :
    QuaternionicSymmetry.delta S.quaternionicDimension + 1 ≤
      ManifoldQuaternionicKillingFields.killingDimension P.tangent := by
  obtain ⟨s, hs, A, _, C, hCanonical⟩ :=
    exists_normalized_contact_canonical hT1 hGeneral S P heq38 hn.1
  let R := rescaleCompact P s hs
  letI : HasSheafify (Opens.grothendieckTopology
      (TopCat.of (SphereBundleTotal R.tangent))) (ModuleCat.{0} ℂ) :=
    SheafComplexSheafification.topCatHasSheafify
      (TopCat.of (SphereBundleTotal R.tangent))
  letI : HasExt.{1} (TopCat.Sheaf (ModuleCat.{0} ℂ)
      (TopCat.of (SphereBundleTotal R.tangent))) :=
    HasExt.standard _
  have hSW := hEquation S R A C
  have hH := swCohomology_of_generalContact R C hCohom hGeneral
    hn.1 S.real_finrank
  rcases hH with ⟨hfinite, hKodairaPositive, hKodairaNegative, hSerre,
    ⟨hSalamon⟩⟩
  have hpositive := virtual_positive_two_twelve S R hsource hsp heq38
    S.quaternionicDimension hn rfl
  have hvirtual := actual_virtual_eq_sections_sub_delta S R A C hSW
    ⟨hn.1, by omega⟩ hCanonical (Classical.choice inferInstance) hfinite
    (hKodairaPositive 0 (by omega))
    (hKodairaPositive 1 (by omega)) hKodairaNegative hSerre
  rw [hvirtual] at hpositive
  have hnat : QuaternionicSymmetry.delta S.quaternionicDimension <
      Module.finrank ℂ (HolomorphicTwistSections R.tangent R.connection
        C.contact.line 1) := by
    exact_mod_cast (show (QuaternionicSymmetry.delta S.quaternionicDimension : ℝ) <
      (Module.finrank ℂ (HolomorphicTwistSections R.tangent R.connection
        C.contact.line 1) : ℝ) by linarith)
  rw [hSalamon.finrank_eq,
    ManifoldQuaternionicKillingFields.complexKillingFields_finrank] at hnat
  have hkill : QuaternionicSymmetry.delta S.quaternionicDimension + 1 ≤
      ManifoldQuaternionicKillingFields.killingDimension R.tangent := by omega
  simpa only [R, killingDimension_rescaleCompact P s hs] using hkill

end
end QuaternionicSymmetry.ManifoldSWNormalizedKillingBound
