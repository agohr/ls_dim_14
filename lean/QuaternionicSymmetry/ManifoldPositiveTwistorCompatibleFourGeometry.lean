import QuaternionicSymmetry.ManifoldPositiveSelfDualEinsteinFourGeometry

/-! The orientation-compatible four-dimensional boundary. The existing
`PositiveSelfDualEinsteinFourGeometry` encodes the vanishing of the Weyl half
opposite to `Q` in one convention; it must not be used to claim integrability
of the existing twistor sphere `S(Q)`. Here the corrected Weyl curvature
*commutes* with every quaternionic generator. In four dimensions this is the
vanishing of its `Q` half, the convention compatible with `S(Q)`. The metric,
Einstein equation, positive scalar curvature and actual rank-three
orientation remain explicit. No complex twistor atlas is claimed. -/
namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicScalarCurvature
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The Weyl curvature in the Einstein four-dimensional normalization,
evaluated on one tangent vector. The sign agrees with the existing
`PositiveSelfDualEinsteinFourGeometry` curvature convention. -/
def correctedWeylVector
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v w : E) : E :=
  adaptedCurvature P.tangent P.connection p y hy u v w -
    (localScalarCurvature P.tangent P.connection p y hy / 12) •
      ((inner ℝ v w) • u - (inner ℝ u w) • v)

/-- A genuine four-dimensional positive Einstein metric whose Weyl
endomorphisms commute with the actual quaternionic span. Via the
`so(4)=su(2)_Q⊕su(2)_{Q^op}` splitting, this is the orientation convention
where the Weyl half acting on `Q` vanishes, so it is the candidate relevant
to the existing `S(Q)` almost-complex twistor construction. -/
structure PositiveTwistorCompatibleFourGeometry extends
    PositiveQuaternionicKahlerGeometry (E := E) (M := M) where
  realDimension : Module.finrank ℝ E = 4
  einstein : ∀ (p : M) (y : E)
      (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E),
      localRicci tangent connection p y hy v w =
        (localScalarCurvature tangent connection p y hy / 4) * inner ℝ v w
  oppositeWeyl : ∀ (p : M) (y : E)
      (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E)
      (a : Fin 3 → ℝ) (w : E),
      correctedWeylVector toPositiveQuaternionicKahlerGeometry p y hy u v
          (synth (tangent.reduction.Q (achart E p)) a w) =
        synth (tangent.reduction.Q (achart E p)) a
          (correctedWeylVector toPositiveQuaternionicKahlerGeometry
            p y hy u v w)

/-- The compact connected package used only after a genuine compact fixed
component has been constructed. These are topology facts about its actual
underlying manifold, not part of the four-dimensional source input. -/
structure CompactConnectedPositiveTwistorCompatibleFourGeometry extends
    PositiveTwistorCompatibleFourGeometry (E := E) (M := M) where
  compact : IsCompact (Set.univ : Set M)
  connected : IsPreconnected (Set.univ : Set M)

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourGeometry
