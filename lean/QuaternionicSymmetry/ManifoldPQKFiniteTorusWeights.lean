import QuaternionicSymmetry.ManifoldQuaternionicContactPowerFromSources
import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmpleRescaled

/-! Finiteness of actual geometric torus-fixed weights on a genuine compact
positive quaternionic-Kähler manifold, using only registered literature
inputs. No eigenbasis, contact ampleness, or tangent continuity is assumed.
The arbitrary-scale theorem uses an explicitly constructed positive homothety.
It does not identify fixed weights between two metrics or prove full span. -/
namespace QuaternionicSymmetry.ManifoldPQKFiniteTorusWeights

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldQuaternionicScalarCurvature ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicTorusAction ManifoldQuaternionicActualWeightHull
open ManifoldQuaternionicContactPowerFromSources
open ManifoldTwistorPositiveContactAmple
open ManifoldTwistorPositiveRicciInput HolomorphicPositiveLineKodairaSource
open CompactTorusEigenbasisSource TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem normalized_actual_weights_finite_from_sources
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (T : ContinuousTorusAction P.tangent r) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    (actualIntegralWeights P.tangent hR3 T).Finite ∧
      (actualRealWeights P.tangent hR3 T).Finite := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  obtain ⟨B,C,hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  exact actual_weights_finite_of_ample P.tangent hR3 hFinite hEigen hCircle
    T P.connection B C.contact hAmple

theorem exists_rescale_actual_weights_finite_from_sources
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      ∀ (r : ℕ) (T : ContinuousTorusAction (rescaleCompact P s hs).tangent r),
        letI : CompactSpace M := ⟨P.compact⟩
        letI : PreconnectedSpace M := ⟨P.connected⟩
        (actualIntegralWeights (rescaleCompact P s hs).tangent hR3 T).Finite ∧
          (actualRealWeights (rescaleCompact P s hs).tangent hR3 T).Finite := by
  obtain ⟨s,hs,hScalar⟩ := exists_normalized_scalar S P heq38 hn
  refine ⟨s,hs,fun r T => ?_⟩
  exact normalized_actual_weights_finite_from_sources hR3 hFinite hEigen hCircle
    hT1 hKodaira (rescaleCompact P s hs)
    S.quaternionicDimension hn S.real_finrank hScalar T

end
end QuaternionicSymmetry.ManifoldPQKFiniteTorusWeights
