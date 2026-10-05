import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrientation

/-! Actual orthogonal lifts of the rank-three quaternionic gauge from
adapted tangent-frame transitions. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicUnitaryNormalizer

open VectorBundleFrameTransitions
  QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
  QuaternionicSymmetry.ManifoldQuaternionicFourFormTransitions
  QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrientation
open scoped ContDiff Manifold

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

/-- Each actual adapted tangent transition is an orthogonal linear
equivalence of the model tangent space. -/
def frameTransitionIsometry (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) : E ≃ₗᵢ[ℝ] E where
  toLinearEquiv := (Q.frameTransition i j x hi hj).toLinearEquiv
  norm_map' v := by
    have h := Q.frameTransition_inner i j x hi hj v v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    change ‖(Q.frameTransition i j x hi hj).toLinearEquiv v‖ ^ 2 = ‖v‖ ^ 2 at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem frameTransitionIsometry_apply (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) (v : E) :
    frameTransitionIsometry Q i j x hi hj v = Q.frames.coordChange i j x v := rfl

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem frameTransitionIsometry_comp (i j k : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (hk : x ∈ Q.frames.adaptedCore.baseSet k) :
    (frameTransitionIsometry Q i j x hi hj).trans
      (frameTransitionIsometry Q j k x hj hk) =
        frameTransitionIsometry Q i k x hi hk := by
  ext v
  simpa only [frameTransitionIsometry_apply] using
    Q.frames.coordChange_comp i j k x hi hj hk v

/-- The orthogonal lift conjugates the first local quaternionic three-plane
onto the second. Its induced SO(3) action is the coefficient transition. -/
theorem frameTransitionIsometry_adjoint (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) (a : Fin 3 → ℝ) :
    QuaternionicFrameReduction.synth (Q.reduction.Q j)
      (Q.reduction.rankThreeCoordChange i j x a) =
      (transitionAtlas Q.frames.adaptedCore).adjointCoordChange i j x
        (QuaternionicFrameReduction.synth (Q.reduction.Q i) a) :=
  synth_rankThreeCoordChange Q i j x hi hj a

theorem frameTransitionIsometry_SO3 (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    rotationMatrix Q i j x ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  rotationMatrix_specialOrthogonal Q i j x hi hj

end
end QuaternionicSymmetry.ManifoldQuaternionicUnitaryNormalizer
