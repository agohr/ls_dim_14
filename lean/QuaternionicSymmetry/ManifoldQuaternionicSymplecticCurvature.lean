import QuaternionicSymmetry.ManifoldQuaternionicCurvatureProjection
import QuaternionicSymmetry.ContinuousLinearConstraintDerivative

/-! Quaternion-linearity of the actual symplectic curvature, proved by
differentiating the connection's constant quaternionic commutation laws. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicSymplecticCurvature

open ManifoldQuaternionicConnectionSplitting ManifoldQuaternionicConnection
  ManifoldQuaternionicAdjointConnection QuaternionicLieAlgebraProjection
  VectorBundleFrameTransitions.QuaternionicFrameReduction
  ContinuousLinearConstraintDerivative
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem fderiv_symplecticConnection_commutes (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (a : Fin 3 → ℝ) :
    fderiv ℝ (symplecticConnection Q D p) y u v * synth (Q.reduction.Q (achart E p)) a =
      synth (Q.reduction.Q (achart E p)) a * fderiv ℝ (symplecticConnection Q D p) y u v := by
  let T := synth (Q.reduction.Q (achart E p)) a
  let L : (E →L[ℝ] (E →L[ℝ] E)) →L[ℝ] (E →L[ℝ] E) :=
    (commutatorMap.flip T).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) v)
  have hd : DifferentiableAt ℝ (symplecticConnection Q D p) y :=
    ((symplecticConnection_smooth Q D p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  have hz := annihilates_fderiv L (symplecticConnection Q D p) y u hd (by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy] with z hz
    change symplecticConnection Q D p z v * T - T * symplecticConnection Q D p z v = 0
    exact sub_eq_zero.mpr (symplecticConnection_commutes Q D p z v hz a))
  exact sub_eq_zero.mp hz

theorem symplecticCurvature_commutes (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (a : Fin 3 → ℝ) :
    LocalConnection.curvature (symplecticConnection Q D p) y u v *
        synth (Q.reduction.Q (achart E p)) a =
      synth (Q.reduction.Q (achart E p)) a *
        LocalConnection.curvature (symplecticConnection Q D p) y u v := by
  have hd₁ := fderiv_symplecticConnection_commutes Q D p y u v hy a
  have hd₂ := fderiv_symplecticConnection_commutes Q D p y v u hy a
  have hc := commutator_commutes_synth (Q.reduction.Q (achart E p))
    (symplecticConnection Q D p y u) (symplecticConnection Q D p y v)
    (symplecticConnection_commutes Q D p y u hy)
    (symplecticConnection_commutes Q D p y v hy) a
  rw [LocalConnection.curvature_apply]
  have he : ∀ A B C F : E →L[ℝ] E, A - B + C - F = (A - B) + (C - F) := by
    intros; abel
  rw [he, add_mul, mul_add, sub_mul, mul_sub, hd₁, hd₂, hc]

end
end QuaternionicSymmetry.ManifoldQuaternionicSymplecticCurvature
