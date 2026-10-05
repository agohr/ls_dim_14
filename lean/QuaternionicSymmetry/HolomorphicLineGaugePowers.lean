import QuaternionicSymmetry.HolomorphicLineGauge

/-! Tensor powers of genuine all-overlap holomorphic line gauges. This is
the bundle-level operation needed before acting on sections of a very ample
power; it does not replace that section space by powers of individual
sections of the original line.
-/

namespace QuaternionicSymmetry.HolomorphicLineGauge

open HolomorphicLinePowers
open scoped Manifold ContDiff
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  {IB : ModelWithCorners ℂ F H} {ι κ : Type*}

/-- Raise both local gauge scalars to the same tensor power. Every overlap
law and inverse law follows from the original gauge; neither is assumed. -/
def GaugeIso.power {Z : VectorBundleCore ℂ B ℂ ι}
    {W : VectorBundleCore ℂ B ℂ κ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W) (k : ℕ) :
    GaugeIso (IB := IB) (powerCore Z k) (powerCore W k) where
  forward i a x := e.forward i a x ^ k
  backward a i x := e.backward a i x ^ k
  forward_holomorphic i a := (e.forward_holomorphic i a).pow k
  backward_holomorphic a i := (e.backward_holomorphic a i).pow k
  forward_compat i j a b x hx := by
    have h := congrArg (fun z : ℂ => z ^ k) (e.forward_compat i j a b x hx)
    simpa only [transitionScalar, powerCore, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, mul_pow] using h
  backward_compat a b i j x hx := by
    have h := congrArg (fun z : ℂ => z ^ k) (e.backward_compat a b i j x hx)
    simpa only [transitionScalar, powerCore, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, mul_pow] using h
  left_inverse i a x hx := by
    simpa only [mul_pow, one_pow] using
      congrArg (fun z : ℂ => z ^ k) (e.left_inverse i a x hx)
  right_inverse a i x hx := by
    simpa only [mul_pow, one_pow] using
      congrArg (fun z : ℂ => z ^ k) (e.right_inverse a i x hx)

end
end QuaternionicSymmetry.HolomorphicLineGauge
