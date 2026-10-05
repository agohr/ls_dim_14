import QuaternionicSymmetry.ManifoldSWNormalizedKillingBound
import QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput

/-! Transfer the source-only virtual-character lower bound from actual
Killing fields to the Lie algebra of the full Riemannian isometry group.
This still does not identify the quaternionic-preserving subgroup. -/
namespace QuaternionicSymmetry.ManifoldSWLieDimensionBound
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldSWNormalizedKillingBound
open ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldSWEquation22SourceContract
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [T2Space M] [SecondCountableTopology M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

/-- The full isometry group carries sourced BG-R3/BG-R4 Lie structure,
and its actual tangent-at-identity dimension satisfies the Stage 2
numerical lower bound. H1 is used only at quaternionic dimensions 13–14. -/
theorem full_isometry_lie_dimension_lower_bound_from_sources
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedComplexContactExistence.{0,0})
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hR3 : IsometryLieSource.{0,0})
    (hR4 : KillingLieSource.{0,0})
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 14) :
    letI : PreconnectedSpace M := ⟨P.connected⟩
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    ∃ (V : Type) (hNorm : NormedAddCommGroup V),
      letI : NormedAddCommGroup V := hNorm
      ∃ (hSpace : NormedSpace ℝ V),
        letI : NormedSpace ℝ V := hSpace
        ∃ (hFinite : FiniteDimensional ℝ V)
          (hChart : ChartedSpace V (M ≃ᵢ M)),
          letI : FiniteDimensional ℝ V := hFinite
          letI : ChartedSpace V (M ≃ᵢ M) := hChart
          IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) ∧
          LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) ∧
          ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
            (fun p : (M ≃ᵢ M) × M => p.1 p.2) ∧
          QuaternionicSymmetry.delta S.quaternionicDimension + 1 ≤
            Module.finrank ℝ (TangentSpace 𝓘(ℝ,V) (1 : M ≃ᵢ M)) := by
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  have hBound := killing_dimension_lower_bound_from_sources S P hsource hAmann
    hsp heq38 hT1 hGeneral hEquation hCohom hn
  obtain ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction, hKilling⟩ :=
      isometryLieKilling_of_sources P.tangent hR3 hR4
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  have hDim := tangent_finrank_eq_killingDimension P.tangent hChart hKilling
  refine ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction, ?_⟩
  rwa [hDim]

/-- In the C12 range the full-isometry Lie-algebra bound has no Amann H1
premise. The BG-R3/R4 contracts only identify the already constructed
actual Lie algebra with the actual Killing fields. -/
theorem full_isometry_lie_dimension_lower_bound_c12_from_sources
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedComplexContactExistence.{0,0})
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hR3 : IsometryLieSource.{0,0})
    (hR4 : KillingLieSource.{0,0})
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 12) :
    letI : PreconnectedSpace M := ⟨P.connected⟩
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    ∃ (V : Type) (hNorm : NormedAddCommGroup V),
      letI : NormedAddCommGroup V := hNorm
      ∃ (hSpace : NormedSpace ℝ V),
        letI : NormedSpace ℝ V := hSpace
        ∃ (hFinite : FiniteDimensional ℝ V)
          (hChart : ChartedSpace V (M ≃ᵢ M)),
          letI : FiniteDimensional ℝ V := hFinite
          letI : ChartedSpace V (M ≃ᵢ M) := hChart
          IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) ∧
          LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) ∧
          ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
            (fun p : (M ≃ᵢ M) × M => p.1 p.2) ∧
          QuaternionicSymmetry.delta S.quaternionicDimension + 1 ≤
            Module.finrank ℝ (TangentSpace 𝓘(ℝ,V) (1 : M ≃ᵢ M)) := by
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  have hBound := killing_dimension_lower_bound_c12_from_sources S P hsource
    hsp heq38 hT1 hGeneral hEquation hCohom hn
  obtain ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction, hKilling⟩ :=
      isometryLieKilling_of_sources P.tangent hR3 hR4
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  have hDim := tangent_finrank_eq_killingDimension P.tangent hChart hKilling
  refine ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction, ?_⟩
  rwa [hDim]

end
end QuaternionicSymmetry.ManifoldSWLieDimensionBound
