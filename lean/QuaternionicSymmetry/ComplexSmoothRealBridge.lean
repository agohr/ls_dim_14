import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic

/-! A real-smooth complex-differentiable map has a continuous complex
derivative: its complex derivative is the inverse image under the isometric
scalar-restriction embedding of the real derivative. -/

namespace QuaternionicSymmetry.ComplexSmoothRealBridge

open ContinuousLinearMap
open Topology
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The C¹ base of the real-smooth-to-complex-smooth upgrade, in arbitrary
complex Banach spaces. -/
theorem contDiff_one_of_real_complex
    {f : E → F} (hReal : ContDiff ℝ 1 f)
    (hComplex : Differentiable ℂ f) : ContDiff ℂ 1 f := by
  apply contDiff_one_iff_fderiv.mpr
  constructor
  · exact hComplex
  · let R := ContinuousLinearMap.restrictScalarsIsometry ℂ E F ℝ ℝ
    have hR : IsEmbedding (R : (E →L[ℂ] F) → (E →L[ℝ] F)) :=
      R.isometry.isEmbedding
    apply hR.continuous_iff.mpr
    have hfun : (R ∘ fun x => fderiv ℂ f x) = fderiv ℝ f := by
      funext x
      exact (hComplex x).fderiv_restrictScalars ℝ |>.symm
    rw [hfun]
    exact hReal.continuous_fderiv (by norm_num)

/-- The same derivative-topology argument works locally on an open subset,
which is the form needed for manifold extended charts. -/
theorem contDiffOn_one_of_real_complex
    {f : E → F} {s : Set E} (hs : IsOpen s)
    (hReal : ContDiffOn ℝ 1 f s)
    (hComplex : DifferentiableOn ℂ f s) : ContDiffOn ℂ 1 f s := by
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ)
    (n := 0) hs).2
  refine ⟨hComplex, by simp, ?_⟩
  apply contDiffOn_zero.mpr
  let R := ContinuousLinearMap.restrictScalarsIsometry ℂ E F ℝ ℝ
  have hR : IsEmbedding (R : (E →L[ℂ] F) → (E →L[ℝ] F)) :=
    R.isometry.isEmbedding
  apply hR.continuousOn_iff.mpr
  have hfun : Set.EqOn (R ∘ fun x => fderiv ℂ f x)
      (fderiv ℝ f) s := by
    intro x hx
    exact ((hComplex x hx).differentiableAt (hs.mem_nhds hx)).fderiv_restrictScalars ℝ
      |>.symm
  exact (hReal.continuousOn_fderiv_of_isOpen hs (by norm_num)).congr hfun

end
end QuaternionicSymmetry.ComplexSmoothRealBridge
