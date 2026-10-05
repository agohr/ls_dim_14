import QuaternionicSymmetry.QuaternionicLieAlgebraProjection
import QuaternionicSymmetry.ManifoldQuaternionicFourFormConnection

/-! The smooth scalar and quaternion-linear parts of an actual compatible
tangent connection. The decomposition is derived from its induced rank-three
connection rather than supplied as extra data. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicConnectionSplitting

open QuaternionicLieAlgebraProjection QuaternionicInfinitesimalSplitting
  ManifoldQuaternionicConnection ManifoldQuaternionicAdjointConnection
  ManifoldQuaternionicFourFormConnection ManifoldQuaternionicMetric
  VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def scalarConnection (p : M) : ConnectionForm (E := E) := fun y =>
  (scalarProjection (Q.reduction.Q (achart E p))).comp (D.form p y)

def symplecticConnection (p : M) : ConnectionForm (E := E) := fun y =>
  (symplecticProjection (Q.reduction.Q (achart E p))).comp (D.form p y)

theorem scalarConnection_apply (p : M) (y u : E) :
    scalarConnection Q D p y u =
      scalarPart (Q.reduction.Q (achart E p)) (inducedMatrix Q D p y u) := rfl

theorem symplecticConnection_apply (p : M) (y u : E) :
    symplecticConnection Q D p y u =
      symplecticPart (Q.reduction.Q (achart E p)) (D.form p y u)
        (inducedMatrix Q D p y u) := rfl

theorem connection_sum (p : M) (y : E) :
    symplecticConnection Q D p y + scalarConnection Q D p y = D.form p y := by
  apply ContinuousLinearMap.ext
  intro u
  exact projection_sum (Q.reduction.Q (achart E p)) (D.form p y u)

theorem scalarConnection_smooth (p : M) :
    ContDiffOn ℝ ∞ (scalarConnection Q D p) (extChartAt 𝓘(ℝ, E) p).target := by
  exact contDiffOn_const.clm_comp (D.smooth_form p)

theorem symplecticConnection_smooth (p : M) :
    ContDiffOn ℝ ∞ (symplecticConnection Q D p) (extChartAt 𝓘(ℝ, E) p).target := by
  exact contDiffOn_const.clm_comp (D.smooth_form p)

theorem symplecticConnection_commutes (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (a : Fin 3 → ℝ) :
    symplecticConnection Q D p y u * synth (Q.reduction.Q (achart E p)) a =
      synth (Q.reduction.Q (achart E p)) a * symplecticConnection Q D p y u := by
  rw [symplecticConnection_apply]
  apply symplecticPart_commutes _ _ _ (inducedMatrix_skew Q D p y u hy)
  intro b
  rw [inducedMatrix_mulVec]
  exact (synth_inducedForm Q D p y u hy b).symm

theorem scalarConnection_skew (p : M) (y u v w : E) :
    inner ℝ (scalarConnection Q D p y u v) w +
      inner ℝ v (scalarConnection Q D p y u w) = 0 := by
  rw [scalarConnection_apply]
  exact scalarPart_skew _ _ v w

theorem symplecticConnection_skew (p : M) (y u v w : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inner ℝ (symplecticConnection Q D p y u v) w +
      inner ℝ v (symplecticConnection Q D p y u w) = 0 := by
  rw [symplecticConnection_apply]
  exact symplecticPart_skew _ _ _ (fun v w => D.metric p y u v w hy) v w

end
end QuaternionicSymmetry.ManifoldQuaternionicConnectionSplitting
