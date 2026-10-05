import QuaternionicSymmetry.HolomorphicLineHermitianGauge
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The real part of a holomorphic scalar function is pluriharmonic: its
real Hessian on `v` cancels that on `i v`. This is proved directly from
complex bilinearity of the second derivative, avoiding any dimension-one
shortcut. -/

namespace QuaternionicSymmetry.HolomorphicRealPartLevi

open Complex
open scoped Manifold ContDiff
noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem realPart_levi_zero (g : F → ℂ) (x v : F)
    (hg : ContDiffAt ℂ 2 g x) :
    ((fderiv ℝ (fderiv ℝ (fun y => (g y).re)) x) v) v +
      ((fderiv ℝ (fderiv ℝ (fun y => (g y).re)) x)
        ((Complex.I : ℂ) • v)) ((Complex.I : ℂ) • v) = 0 := by
  let T := iteratedFDeriv ℂ 2 g x
  have hC : T ![(Complex.I : ℂ) • v, (Complex.I : ℂ) • v] =
      -T ![v, v] := by
    have hvect : ![(Complex.I : ℂ) • v, (Complex.I : ℂ) • v] =
        (fun _ : Fin 2 => (Complex.I : ℂ)) • ![v, v] := by
      ext j
      fin_cases j <;> rfl
    rw [hvect]
    change T (fun j : Fin 2 => (Complex.I : ℂ) • (![v, v] j)) = _
    rw [T.map_smul_univ]
    simp
  have hR := hg.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  have hRe := (reCLM : ℂ →L[ℝ] ℝ).iteratedFDeriv_comp_left
    (hg.restrict_scalars ℝ) (i := 2)
    (by norm_num : (2 : ℕ) ≤ (2 : WithTop ℕ∞))
  have hfirst := iteratedFDeriv_two_apply (𝕜 := ℝ)
    (fun y : F => (g y).re) x ![v, v]
  have hsecond := iteratedFDeriv_two_apply (𝕜 := ℝ)
    (fun y : F => (g y).re) x
    ![(Complex.I : ℂ) • v, (Complex.I : ℂ) • v]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hfirst hsecond
  rw [← hfirst, ← hsecond]
  change iteratedFDeriv ℝ 2 (reCLM ∘ g) x ![v, v] +
    iteratedFDeriv ℝ 2 (reCLM ∘ g) x
      ![(Complex.I : ℂ) • v, (Complex.I : ℂ) • v] = 0
  rw [hRe]
  change reCLM (iteratedFDeriv ℝ 2 g x ![v, v]) +
    reCLM (iteratedFDeriv ℝ 2 g x
      ![(Complex.I : ℂ) • v, (Complex.I : ℂ) • v]) = 0
  rw [← hR]
  change reCLM (T ![v, v]) + reCLM
    (T ![(Complex.I : ℂ) • v, (Complex.I : ℂ) • v]) = 0
  rw [hC]
  simp

private theorem logNormSq_levi_zero_of_slit (g : F → ℂ) (x v : F)
    (hg : ContDiffAt ℂ 2 g x) (hslit : g x ∈ Complex.slitPlane) :
    ((fderiv ℝ (fderiv ℝ (fun y => Real.log (Complex.normSq (g y)))) x) v) v +
      ((fderiv ℝ (fderiv ℝ (fun y => Real.log (Complex.normSq (g y)))) x)
        ((Complex.I : ℂ) • v)) ((Complex.I : ℂ) • v) = 0 := by
  have hLog : ContDiffAt ℂ 2 (fun y => Complex.log (g y)) x :=
    (analyticAt_clog hslit).contDiffAt.comp x hg
  have hZero := realPart_levi_zero (fun y => Complex.log (g y)) x v hLog
  have hfun : (fun y : F => Real.log (Complex.normSq (g y))) =
      (2 : ℝ) • (fun y : F => (Complex.log (g y)).re) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_eq_norm_sq,
      Real.log_pow, Complex.log_re]
    ring
  rw [hfun]
  simp only [fderiv_const_smul_field]
  have hSecond := fderiv_const_smul_field (𝕜 := ℝ)
    (f := fderiv ℝ (fun y : F => (Complex.log (g y)).re)) (c := (2 : ℝ))
  rw [hSecond]
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  nlinarith

/-- The logarithm of the squared norm of a nonvanishing holomorphic
scalar has zero Levi Hessian in every complex tangent direction. A sign
change moves a value on the logarithm's branch cut into its slit plane;
the squared norm is unchanged. -/
theorem logNormSq_levi_zero (g : F → ℂ) (x v : F)
    (hg : ContDiffAt ℂ 2 g x) (hne : g x ≠ 0) :
    ((fderiv ℝ (fderiv ℝ (fun y => Real.log (Complex.normSq (g y)))) x) v) v +
      ((fderiv ℝ (fderiv ℝ (fun y => Real.log (Complex.normSq (g y)))) x)
        ((Complex.I : ℂ) • v)) ((Complex.I : ℂ) • v) = 0 := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hne with hslit | hslit
  · exact logNormSq_levi_zero_of_slit g x v hg hslit
  · have hneg := logNormSq_levi_zero_of_slit (fun y => -g y) x v
      hg.neg hslit
    simpa only [Complex.normSq_neg] using hneg

end
end QuaternionicSymmetry.HolomorphicRealPartLevi
