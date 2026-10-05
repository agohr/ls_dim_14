import QuaternionicSymmetry.ManifoldQuaternionicHomothetyMetric
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Metric homotheties between actual, possibly differently presented
manifolds. The witness is a genuine smooth diffeomorphism and a positive
constant in its pullback-metric equation. No classification predicate or
model-existence assumption is introduced. -/

namespace QuaternionicSymmetry.ManifoldMetricHomothety

open ManifoldQuaternionicMetric ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyMetric
open scoped Manifold ContDiff
noncomputable section

variable {E F G M N O : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  [TopologicalSpace O] [ChartedSpace G O] [IsManifold 𝓘(ℝ,G) ∞ O]

/-- The scale is the metric factor, not its square root. Quaternionic
span preservation is not silently included in a metric classification. -/
structure MetricHomothety
    (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (R : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,F)) (M := N) (n := ∞)) where
  map : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞
  scale : ℝ
  scale_pos : 0 < scale
  metric_eq : ∀ (x : M) (v w : TangentSpace 𝓘(ℝ,E) x),
    R.tangentMetricForm (map x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (map : M → N) x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (map : M → N) x w) =
      scale * Q.tangentMetricForm x v w

variable
  (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (R : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,F)) (M := N) (n := ∞))
  (S : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,G)) (M := O) (n := ∞))

def MetricHomothety.refl : MetricHomothety Q Q where
  map := Diffeomorph.refl 𝓘(ℝ,E) M ∞
  scale := 1
  scale_pos := zero_lt_one
  metric_eq := by
    intro x v w
    simp [mfderiv_id]

/-- The chain rule composes the actual metric equations, with the product
of the two positive metric factors. -/
def MetricHomothety.trans (f : MetricHomothety Q R)
    (g : MetricHomothety R S) : MetricHomothety Q S where
  map := f.map.trans g.map
  scale := g.scale * f.scale
  scale_pos := mul_pos g.scale_pos f.scale_pos
  metric_eq := by
    intro x v w
    change S.tangentMetricForm (g.map (f.map x))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G)
        ((g.map : N → O) ∘ (f.map : M → N)) x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G)
        ((g.map : N → O) ∘ (f.map : M → N)) x w) = _
    rw [mfderiv_comp x
      (g.map.contMDiff.mdifferentiable (by simp) (f.map x))
      (f.map.contMDiff.mdifferentiable (by simp) x)]
    exact (g.metric_eq (f.map x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (f.map : M → N) x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (f.map : M → N) x w)).trans
        ((congrArg (fun r : ℝ => g.scale * r) (f.metric_eq x v w)).trans
          (mul_assoc g.scale f.scale (Q.tangentMetricForm x v w)).symm)

/-- Inverting the diffeomorphism inverts the metric factor. -/
def MetricHomothety.symm (f : MetricHomothety Q R) : MetricHomothety R Q where
  map := f.map.symm
  scale := f.scale⁻¹
  scale_pos := inv_pos.mpr f.scale_pos
  metric_eq := by
    intro y v w
    have h := f.metric_eq (f.map.symm y)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (f.map.symm : N → M) y v)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (f.map.symm : N → M) y w)
    have hid : ((f.map : M → N) ∘ (f.map.symm : N → M)) = id := by
      funext x
      exact f.map.apply_symm_apply x
    have hderiv :
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (f.map : M → N) (f.map.symm y)).comp
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (f.map.symm : N → M) y) =
          ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ,F) y) := by
      have hc := mfderiv_comp y
        (f.map.contMDiff.mdifferentiable (by simp) (f.map.symm y))
        (f.map.symm.contMDiff.mdifferentiable (by simp) y)
      rw [hid, mfderiv_id] at hc
      exact hc.symm
    have hcancel (u : TangentSpace 𝓘(ℝ,F) y) :
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (f.map : M → N) (f.map.symm y)
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (f.map.symm : N → M) y u) = u := by
      exact congrArg (fun L : F →L[ℝ] F => L u) hderiv
    rw [f.map.apply_symm_apply] at h
    have hMetric := h.symm.trans
      (congrArg₂ (fun a b => R.tangentMetricForm y a b) (hcancel v) (hcancel w))
    exact (eq_inv_mul_iff_mul_eq₀ (ne_of_gt f.scale_pos)).2 hMetric

/-- The already constructed frame rescaling has exactly this actual
metric-homothety witness, via the identity diffeomorphism. -/
def rescaleHomothety (s : ℝ) (hs : 0 < s) :
    MetricHomothety Q (rescaleMetric Q s (ne_of_gt hs)) where
  map := Diffeomorph.refl 𝓘(ℝ,E) M ∞
  scale := s ^ 2
  scale_pos := pow_pos hs 2
  metric_eq := by
    intro x v w
    simpa [mfderiv_id] using tangentMetricForm_rescale Q s (ne_of_gt hs) x v w

/-- A classification witness for a normalized homothety gives a witness
for the original metric, with its true scale retained. -/
def homothety_of_rescaled_source (s : ℝ) (hs : 0 < s)
    (f : MetricHomothety (rescaleMetric Q s (ne_of_gt hs)) R) :
    MetricHomothety Q R :=
  MetricHomothety.trans Q (rescaleMetric Q s (ne_of_gt hs)) R
    (rescaleHomothety Q s hs) f

end
end QuaternionicSymmetry.ManifoldMetricHomothety
