import QuaternionicSymmetry.ManifoldTwistorSelectedComponentRestrictionFromSources

/-! An actual extreme vertical contact-line character of a faithful
positive-rank isometry torus is nonzero. This is deduced from the already
proved symmetric finite weight hull; it is not a fresh source premise. -/
namespace QuaternionicSymmetry.ManifoldTwistorSelectedExtremeWeightNonzero

open ManifoldPositiveQuaternionicWeightHull
open ManifoldQuaternionicMaximalTorusAction ManifoldQuaternionicTorusAction
open ManifoldQuaternionicActualWeightHull
open ManifoldQuaternionicSpanSymmetry
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldTwistorPositiveRicciInput
open HolomorphicPositiveLineKodairaSource ProjectiveAnalyticAlgebraicSources
open CompactTorusEigenbasisSource TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [LocallyCompactSpace M] [CompactSpace M] [PreconnectedSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem selected_extreme_character_ne_zero_from_sources
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
    {r : ℕ} (T : CompactLieTorusInputs.TorusEmbedding
      (QuaternionicIsometries P.tangent) r) (hr : 0 < r)
    (ν : Fin r → ℤ)
    (hExtreme : (fun i => (ν i : ℝ)) ∈
      (convexHull ℝ (actualRealWeights P.tangent hR3
        (actionOfEmbedding P.tangent T))).extremePoints ℝ) :
    ν ≠ 0 := by
  obtain ⟨_,_,_,hAll,_⟩ := normalized_actual_weight_hull_from_sources
    hT1 hKodaira hR3 hFinite hEigen hCircle
    P n hn hDim hScalar (actionOfEmbedding P.tangent T)
    (actionOfEmbedding_faithful P.tangent T) hr
  intro hzero
  apply hAll (fun i => (ν i : ℝ)) hExtreme
  funext i
  simp [hzero]

end
end QuaternionicSymmetry.ManifoldTwistorSelectedExtremeWeightNonzero
