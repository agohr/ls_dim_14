import QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry

/-! Intrinsic Riemannian symmetry is invariant under an actual metric
homothety, even when the two manifolds use different model spaces. -/

namespace QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry

open ManifoldMetricHomothety ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N]
  {Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞)}
  {R : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,F)) (M := N) (n := ∞)}

/-- Conjugating an actual point isometry by a metric homothety gives an
actual point isometry of the target metric. -/
def PointSymmetry.transport (f : MetricHomothety Q R) (y : N)
    (s : PointSymmetry Q (f.map.symm y)) : PointSymmetry R y := by
  let t : MetricHomothety R R :=
    MetricHomothety.trans R Q R (MetricHomothety.symm Q R f)
      (MetricHomothety.trans Q Q R s.map f)
  have htScale : t.scale = 1 := by
    dsimp [t, MetricHomothety.trans, MetricHomothety.symm]
    rw [s.scale_one]
    simp [mul_inv_cancel₀ (ne_of_gt f.scale_pos)]
  have htFixed : t.map y = y := by
    change f.map (s.map.map (f.map.symm y)) = y
    rw [s.fixed, f.map.apply_symm_apply]
  refine ⟨t, htScale, htFixed, ?_⟩
  intro v
  let x : M := f.map.symm y
  let A := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (f.map.symm : N → M) y
  let B := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (f.map : M → N) x
  have hBA : B.comp A = ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ,F) y) := by
    have hcomp := mfderiv_comp y
      (f.map.contMDiff.mdifferentiable (by simp) x)
      (f.map.symm.contMDiff.mdifferentiable (by simp) y)
    have hid : ((f.map : M → N) ∘ (f.map.symm : N → M)) = id := by
      funext z
      exact f.map.apply_symm_apply z
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F)
      ((f.map : M → N) ∘ (f.map.symm : N → M)) y = B.comp A at hcomp
    rw [hid, mfderiv_id] at hcomp
    exact hcomp.symm
  have hBA_apply (w : TangentSpace 𝓘(ℝ,F) y) : B (A w) = w := by
    exact congrArg (fun L : F →L[ℝ] F => L w) hBA
  have hInner :
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E)
        ((s.map.map : M → M) ∘ (f.map.symm : N → M)) y v =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (s.map.map : M → M) x (A v) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun L : F →L[ℝ] E => L v) (mfderiv_comp y
        (s.map.map.contMDiff.mdifferentiable (by simp) x)
        (f.map.symm.contMDiff.mdifferentiable (by simp) y))
  have hOuter :
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F)
        ((f.map : M → N) ∘ ((s.map.map : M → M) ∘
          (f.map.symm : N → M))) y v =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (f.map : M → N)
        (s.map.map x)
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E)
          ((s.map.map : M → M) ∘ (f.map.symm : N → M)) y v) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun L : F →L[ℝ] F => L v) (mfderiv_comp y
        (f.map.contMDiff.mdifferentiable (by simp) (s.map.map x))
        ((s.map.map.contMDiff.comp f.map.symm.contMDiff).mdifferentiable (by simp) y))
  have hderiv :
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (t.map : N → N) y v =
        B (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
          (s.map.map : M → M) x (A v)) := by
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F)
      ((f.map : M → N) ∘ ((s.map.map : M → M) ∘
        (f.map.symm : N → M))) y v = _
    rw [hOuter, hInner, s.fixed]
  rw [hderiv, s.deriv_neg, map_neg, hBA_apply]

theorem isRiemannianSymmetric_of_metricHomothety
    (f : MetricHomothety Q R) (hQ : IsRiemannianSymmetric Q) :
    IsRiemannianSymmetric R := by
  intro y
  obtain ⟨s⟩ := hQ (f.map.symm y)
  exact ⟨s.transport f y⟩

theorem isRiemannianSymmetric_iff_metricHomothety
    (f : MetricHomothety Q R) :
    IsRiemannianSymmetric Q ↔ IsRiemannianSymmetric R := by
  constructor
  · exact isRiemannianSymmetric_of_metricHomothety f
  · exact isRiemannianSymmetric_of_metricHomothety
      (MetricHomothety.symm Q R f)

end
end QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry
