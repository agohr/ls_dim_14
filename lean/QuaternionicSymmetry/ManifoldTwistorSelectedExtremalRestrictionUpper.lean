import QuaternionicSymmetry.ManifoldTwistorSelectedComponentRestrictionBound
import QuaternionicSymmetry.ManifoldQuaternionicBWWExtremalApplication
import QuaternionicSymmetry.ManifoldQuaternionicContactFixedWeightSpan

/-! Actual unpowered extremal restriction at most one. Ampleness and
faithfulness derive zero-weight exclusion; BWW supplies the actual ambient
restriction surjection; the selected root estimate comes from the SAME
contact atlas and torus. No restriction or nonzero-character premise remains. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedExtremalRestrictionUpper

open ManifoldTwistorSelectedComponentRestrictionBound
open ManifoldQuaternionicContactComponentRestriction
open ManifoldQuaternionicContactComponentWeightBound
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorSelectedHamiltonianEigenbasis
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTorusContactSections
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicLineCoreAmpleFiniteMap TorusWeightSeparation
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [LocallyCompactSpace M]
  [CompactSpace M] [PreconnectedSpace M]
  [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
  (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
  {r : ℕ} (T : TorusEmbedding
    (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)

/-- Pass the SAME selected root bound to the literal contact-section
representation used by the normalized extremal-isolation induction. -/
theorem contactWeight_bound_of_selected_root_bound
    (hRoot : letI := A.charts
      ∀ ν : Fin r → ℤ, ν ≠ 0 →
        Module.finrank ℂ (selectedSectionWeightSpace P n A C T ν) ≤ 1) :
    letI := A.charts
    ∀ ν : Fin r → ℤ, ν ≠ 0 →
      Module.finrank ℂ (contactWeightSubmodule P.tangent
        (actionOfEmbedding P.tangent T) P.connection A C.contact ν) ≤ 1 := by
  letI := A.charts
  intro ν hν
  rw [contactWeightSubmodule_eq_selected P n A C T ν]
  exact hRoot ν hν

theorem restricted_extremal_finrank_le_one_from_sources
    (hBWW : GeneralBWWAnalyticExtremalSource.AnalyticExtremalRestrictionAndSmallSections)
    (hLee : GeneralSmoothMapSource.LeeEmbeddedCodomainRestrictionTheorem)
    (hr : 0 < r)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    (hAmple : letI := A.charts; letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (hPic : letI := A.charts
      Function.Bijective (fun m : ℤ =>
        (Quotient.mk _ (contactLineCore P.tangent P.connection C.contact.line) :
          HolomorphicLineCoreClasses.CoreClass.{0} (B := SphereBundleTotal P.tangent)
            𝓘(ℂ,ComplexTwistorModel n)) ^ m))
    (hRoot : letI := A.charts
      ∀ ν : Fin r → ℤ, ν ≠ 0 →
        Module.finrank ℂ (selectedSectionWeightSpace P n A C T ν) ≤ 1)
    (z : SphereBundleTotal P.tangent)
    (hz : ∀ t, (actionOfEmbedding P.tangent T).representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter P.tangent hR3
      (actionOfEmbedding P.tangent T) z hz t = weightCharacter ν t)
    (hExt : TorusIntegralVertexExposure.realWeight ν ∈
      (convexHull ℝ (ManifoldQuaternionicActualWeightHull.actualRealWeights
        P.tangent hR3 (actionOfEmbedding P.tangent T))).extremePoints ℝ)
    {b : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin b))
      (↥(component P.tangent (actionOfEmbedding P.tangent T) z))]
    [IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞
      (↥(component P.tangent (actionOfEmbedding P.tangent T) z))]
    (hIncl : letI := A.charts
      ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (Subtype.val : ↥(component P.tangent
          (actionOfEmbedding P.tangent T) z) → SphereBundleTotal P.tangent))
    (hImm : letI := A.charts
      ∀ y, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin b))
        𝓘(ℝ,ComplexTwistorModel n)
        (Subtype.val : ↥(component P.tangent (actionOfEmbedding P.tangent T) z) →
          SphereBundleTotal P.tangent) y)) :
    letI := A.charts
    Module.finrank ℂ (RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,EuclideanSpace ℂ (Fin b))
      (contactLineCore P.tangent P.connection C.contact.line)
      (Subtype.val : ↥(component P.tangent
        (actionOfEmbedding P.tangent T) z) → SphereBundleTotal P.tangent)
      hIncl) ≤ 1 := by
  letI := A.charts
  letI := A.complexManifold
  have hSpan := ManifoldQuaternionicContactFixedWeightSpan.actualRealWeights_span_eq_top_from_sources
    P.tangent hR3 hFinite hEigen hCircle
    (actionOfEmbedding P.tangent T) (actionOfEmbedding_faithful P.tangent T)
    P.connection A C.contact hAmple
  have hAff := ManifoldQuaternionicContactFixedWeightSpan.actualRealWeights_affineSpan_of_span
    P.tangent hR3 (actionOfEmbedding P.tangent T) hr hSpan
  have hNonzero := ManifoldQuaternionicActualWeightHull.actual_extreme_ne_zero
    P.tangent hR3 (actionOfEmbedding P.tangent T) hr hAff hExt
  have hν0 : ν ≠ 0 := by
    intro heq
    apply hNonzero
    funext i
    simp [TorusIntegralVertexExposure.realWeight, heq]
  obtain ⟨hSurj,_⟩ :=
    ManifoldQuaternionicBWWExtremalApplication.actual_extremal_restriction_and_small_sections_from_sources
      P.tangent P.connection A C.contact (actionOfEmbedding P.tangent T)
      hBWW hR3 hFinite hEigen hCircle hLee hr
      hAmple hPic (actionOfEmbedding_faithful P.tangent T)
      z hz ν hν hExt hIncl hImm
  exact restricted_finrank_le_one_of_selected_weight_bound P n A C T
    hR3 hFinite hEigen hCircle hAmple z hz ν hν hIncl hSurj (hRoot ν hν0)

end
end QuaternionicSymmetry.ManifoldTwistorSelectedExtremalRestrictionUpper
