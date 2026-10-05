import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal

/-! Curvature of the connection induced on the quaternionic rank-three
endomorphism plane. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdjointCurvature

open QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [I.Boundaryless] {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem commutator_jacobi (Γ Δ T : E →L[ℝ] E) :
    commutatorMap Γ (commutatorMap Δ T) -
      commutatorMap Δ (commutatorMap Γ T) =
        commutatorMap (Γ * Δ - Δ * Γ) T := by
  simp only [commutatorMap_apply]
  simp_rw [← ContinuousLinearMap.mul_def]
  noncomm_ring

theorem synth_adjointRepresentation (S : QuaternionicStructure E)
    (Γ : E →L[ℝ] E) (hΓ : PreservesSpan S Γ)
    (a : Fin 3 → ℝ) :
    synth S (adjointRepresentation S Γ a) = commutatorMap Γ (synth S a) := by
  rw [adjointRepresentation_apply, ← commutatorMap_apply]
  apply synth_coeff_of_mem
  exact hΓ _ (synth_mem S a)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem preservesSpan_commutator (S : QuaternionicStructure E)
    (Γ Δ : E →L[ℝ] E)
    (hΓ : PreservesSpan S Γ) (hΔ : PreservesSpan S Δ) :
    PreservesSpan S (Γ * Δ - Δ * Γ) := by
  intro T hT
  rw [← commutator_jacobi Γ Δ T]
  exact (quaternionicSpan S).sub_mem
    (hΓ _ (hΔ _ hT)) (hΔ _ (hΓ _ hT))

theorem adjointRepresentation_commutator (S : QuaternionicStructure E)
    (Γ Δ : E →L[ℝ] E)
    (hΓ : PreservesSpan S Γ) (hΔ : PreservesSpan S Δ) :
    adjointRepresentation S (Γ * Δ - Δ * Γ) =
      adjointRepresentation S Γ * adjointRepresentation S Δ -
        adjointRepresentation S Δ * adjointRepresentation S Γ := by
  apply ContinuousLinearMap.ext
  intro a
  have hleft := synth_adjointRepresentation S (Γ * Δ - Δ * Γ)
    (preservesSpan_commutator S Γ Δ hΓ hΔ) a
  have hrightΓ := synth_adjointRepresentation S Γ hΓ
    (adjointRepresentation S Δ a)
  have hrightΔ := synth_adjointRepresentation S Δ hΔ
    (adjointRepresentation S Γ a)
  have hΓa := synth_adjointRepresentation S Γ hΓ a
  have hΔa := synth_adjointRepresentation S Δ hΔ a
  have heq : synth S (adjointRepresentation S (Γ * Δ - Δ * Γ) a) =
      synth S ((adjointRepresentation S Γ * adjointRepresentation S Δ -
        adjointRepresentation S Δ * adjointRepresentation S Γ) a) := by
    rw [hleft]
    change commutatorMap (Γ * Δ - Δ * Γ) (synth S a) =
      synth S (adjointRepresentation S Γ
        (adjointRepresentation S Δ a) -
          adjointRepresentation S Δ (adjointRepresentation S Γ a))
    conv_rhs => rw [map_sub]
    rw [hrightΓ, hrightΔ, hΔa, hΓa]
    exact (commutator_jacobi Γ Δ (synth S a)).symm
  have h := congrArg (coeff S) heq
  simpa only [coeff_synth] using h

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := I) (M := M) (n := n))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem fderiv_inducedForm (p : M) (y : E)
    (hy : y ∈ (extChartAt I p).target) :
    fderiv ℝ (inducedForm Q D p) y =
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (R3 →L[ℝ] R3)
        (adjointRepresentation (Q.reduction.Q (achart H p)))).comp
        (fderiv ℝ (D.form p) y) := by
  let L := ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (R3 →L[ℝ] R3)
    (adjointRepresentation (Q.reduction.Q (achart H p)))
  have hd : DifferentiableAt ℝ (D.form p) y :=
    ((D.smooth_form p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds hy)
  change fderiv ℝ (L ∘ D.form p) y = L.comp (fderiv ℝ (D.form p) y)
  simpa only [L.fderiv] using
    (fderiv_comp y (g := L) L.differentiableAt hd)

/-- Curvature of the induced rank-three connection is the adjoint action
of the actual tangent curvature, with no independent curvature field. -/
theorem inducedCurvature_eq_adjoint (p : M) (y u v : E)
    (hy : y ∈ (extChartAt I p).target) :
    inducedCurvature Q D p y u v =
      adjointRepresentation (Q.reduction.Q (achart H p))
        (ManifoldQuaternionicConnection.CompatibleTangentConnection.curvature Q D p y u v) := by
  let S := Q.reduction.Q (achart H p)
  let Γ := D.form p y u
  let Δ := D.form p y v
  have hΓ : PreservesSpan S Γ := tangentForm_preservesSpan Q D p y u hy
  have hΔ : PreservesSpan S Δ := tangentForm_preservesSpan Q D p y v hy
  have hLie := adjointRepresentation_commutator S Γ Δ hΓ hΔ
  rw [ManifoldQuaternionicConnection.CompatibleTangentConnection.curvature,
    LocalConnection.curvature_apply]
  rw [inducedCurvature, LocalConnection.curvature_apply,
    fderiv_inducedForm Q D p y hy]
  change adjointRepresentation S (fderiv ℝ (D.form p) y u v) -
      adjointRepresentation S (fderiv ℝ (D.form p) y v u) +
        adjointRepresentation S Γ * adjointRepresentation S Δ -
          adjointRepresentation S Δ * adjointRepresentation S Γ =
      adjointRepresentation S
        (fderiv ℝ (D.form p) y u v - fderiv ℝ (D.form p) y v u +
          Γ * Δ - Δ * Γ)
  calc
    _ = adjointRepresentation S
          (fderiv ℝ (D.form p) y u v - fderiv ℝ (D.form p) y v u) +
        adjointRepresentation S (Γ * Δ - Δ * Γ) := by
          rw [hLie, map_sub]
          abel
    _ = _ := by
      simp only [map_add, map_sub]
      abel

end
end QuaternionicSymmetry.ManifoldQuaternionicAdjointCurvature
