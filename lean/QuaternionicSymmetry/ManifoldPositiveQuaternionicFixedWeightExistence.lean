import QuaternionicSymmetry.ManifoldPositiveQuaternionicComplexTorusActionData
import QuaternionicSymmetry.ManifoldQuaternionicContactExposedWeight
import QuaternionicSymmetry.TorusIntegralGenericCocharacter
import QuaternionicSymmetry.TorusIntegralExposedRefinement
import QuaternionicSymmetry.ManifoldQuaternionicContactNonzeroSectionWeight

/-! Actual torus-fixed twistor points and integral vertical weights exist
on normalized compact positive quaternionic-Kähler manifolds. Existence is
derived from a finite integral cocharacter and a projective orbit limit;
no fixed-point theorem or weight-span conclusion is added as a source.
The first endpoint allows a zero weight. Faithfulness and positive rank
give a nonzero weight in the second endpoint, without a full-span premise. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicFixedWeightExistence

open ManifoldPositiveQuaternionicComplexTorusActionData
open ManifoldQuaternionicContactExposedWeight TorusIntegralGenericCocharacter
open TorusIntegralExposedRefinement ManifoldQuaternionicContactNonzeroSectionWeight
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicTorusAction ManifoldQuaternionicActualWeightHull
open ManifoldTwistorPositiveContactAmple ManifoldTwistorPositiveRicciInput
open HolomorphicPositiveLineKodairaSource ProjectiveAnalyticAlgebraicSources
open CompactTorusEigenbasisSource TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem normalized_actual_weights_nonempty_from_sources
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (A : ContinuousTorusAction P.tangent r) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    (actualIntegralWeights P.tangent hR3 A).Nonempty := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  obtain ⟨B,C,k,hk,hVery,d,b,hGen,μ,ρ,hEig,hRestrict,hProjective⟩ :=
    exists_normalized_twistor_complex_torus_action_with_data
      hT1 hKodaira hR3 hFinite hEigen hCircle
      P n hn hDim hScalar A
  obtain ⟨j,u,hMin,hFace⟩ := exists_exposed_minimum μ
  obtain ⟨ν,hν,_⟩ := exposed_sectionWeight_realized P.tangent
    hR3 hCircle A P.connection B C.contact k hVery
    b hGen μ hEig j u hMin hFace
  exact ⟨ν,hν⟩

/-- A faithful positive-rank torus has a genuinely nonzero vertical weight
at an actual fixed twistor point. This does not assert full weight span. -/
theorem normalized_actual_nonzero_weight_from_sources
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (A : ContinuousTorusAction P.tangent r)
    (hA : A.Faithful) (hr : 0 < r) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    ∃ ν ∈ actualIntegralWeights P.tangent hR3 A, ν ≠ 0 := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  obtain ⟨B,C,k,hk,hVery,d,b,hGen,μ,ρ,hEig,hRestrict,hProjective⟩ :=
    exists_normalized_twistor_complex_torus_action_with_data
      hT1 hKodaira hR3 hFinite hEigen hCircle
      P n hn hDim hScalar A
  have hNonzero := exists_nonzero_sectionWeight_of_nontrivial P.tangent A
    (faithful_positive_rank_nontrivial P.tangent A hA hr)
    P.connection B C.contact k hVery b μ hEig
  obtain ⟨j,u,hj,hMin,hFace⟩ := exists_nonzero_exposed_minimum μ hNonzero
  obtain ⟨ν,hν,heq⟩ := exposed_sectionWeight_realized P.tangent
    hR3 hCircle A P.connection B C.contact k hVery
    b hGen μ hEig j u hMin hFace
  refine ⟨ν,hν,?_⟩
  intro hz
  apply hj
  rw [← heq,hz,smul_zero]

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicFixedWeightExistence
