import QuaternionicSymmetry.ManifoldPositiveQuaternionicFixedWeightExistence
import QuaternionicSymmetry.ManifoldPQKFiniteTorusWeights
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology

/-! The actual fixed-weight set of a faithful positive-rank torus is finite,
contains a nonzero weight, and has no zero extreme point in its real convex
hull. All geometry is on the original normalized PQK manifold. The extreme
point assertion uses actual antipodal symmetry, not a full-span premise. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicWeightHull

open ManifoldPositiveQuaternionicFixedWeightExistence ManifoldPQKFiniteTorusWeights
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicTorusAction ManifoldQuaternionicActualWeightHull
open ManifoldTwistorPositiveRicciInput HolomorphicPositiveLineKodairaSource
open ProjectiveAnalyticAlgebraicSources CompactTorusEigenbasisSource TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem normalized_actual_weight_hull_from_sources
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
    (actualIntegralWeights P.tangent hR3 A).Finite ∧
      (actualRealWeights P.tangent hR3 A).Finite ∧
      (∃ ν ∈ actualIntegralWeights P.tangent hR3 A, ν ≠ 0) ∧
      (∀ w ∈ (convexHull ℝ (actualRealWeights P.tangent hR3 A)).extremePoints ℝ,
        w ≠ 0) ∧
      ((convexHull ℝ (actualRealWeights P.tangent hR3 A)).extremePoints ℝ).Nonempty := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  obtain ⟨hInt,hReal⟩ := normalized_actual_weights_finite_from_sources
    hR3 hFinite hEigen hCircle hT1 hKodaira
    P n hn hDim hScalar A
  have hNonzero := normalized_actual_nonzero_weight_from_sources
    hT1 hKodaira hR3 hFinite hEigen hCircle
    P n hn hDim hScalar A hA hr
  have hRealNonzero : ∃ w ∈ actualRealWeights P.tangent hR3 A, w ≠ 0 := by
    obtain ⟨ν,hν,hne⟩ := hNonzero
    refine ⟨(fun i => (ν i : ℝ)),⟨ν,hν,rfl⟩,?_⟩
    intro hz
    apply hne
    funext i
    have hi : (ν i : ℝ) = 0 := congrFun hz i
    exact_mod_cast hi
  refine ⟨hInt,hReal,hNonzero,?_,?_⟩
  · intro w hw
    exact SymmetricWeightHull.extreme_ne_zero
      (fun v hv => actualRealWeights_neg P.tangent hR3 A hv) hRealNonzero hw
  · apply hReal.isCompact_convexHull.extremePoints_nonempty
    obtain ⟨w,hw,_⟩ := hRealNonzero
    exact ⟨w,subset_convexHull ℝ _ hw⟩

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicWeightHull
