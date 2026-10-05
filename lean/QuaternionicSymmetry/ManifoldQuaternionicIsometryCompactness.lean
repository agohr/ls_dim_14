import QuaternionicSymmetry.ManifoldQuaternionicIsometryClosedFromAction
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-! Compactness of the actual quaternionic isometry group, derived from the
smooth metric-isometry action. This interface is proved below; it is not an
additional field of the final literature boundary. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicSpanSymmetry
open scoped Manifold ContDiff
noncomputable section

def QuaternionicIsometryCompactness : Prop :=
  ∀ {E : Type} {M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [T3Space M] [SecondCountableTopology M]
    [CompactSpace M] [PreconnectedSpace M] [Nonempty M],
    ∀ P : PositiveQuaternionicKahlerGeometry (E := E) (M := M),
    ∀ n : ℕ, 2 ≤ n → Module.finrank ℝ E = 4 * n →
          CompactSpace (QuaternionicIsometries P.tangent)

/-- The closed-subgroup proof removes any need for full-isometry preservation. -/
theorem compactness_of_isometryLie
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0}) :
    QuaternionicIsometryCompactness := by
  intro E M hNorm hInner hFinite hNontrivial hTop hChart hManifold hT3 hSecond
    hCompact hConnected hNonempty P n hn hDim
  exact ManifoldQuaternionicIsometryClosedSubgroup.quaternionicIsometries_compactSpace_of_isometryLie
    P.tangent (hR3 P.tangent)

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
