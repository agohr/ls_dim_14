import QuaternionicSymmetry.GeneralImmersionChartMetricJet
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Symmetry of the genuine ambient Hessian of a smooth chartwise immersion. -/

namespace QuaternionicSymmetry.GeneralImmersionHessianSymmetry

open scoped ContDiff

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hessian_symmetric (f : E → V) (y u v : E)
    (hf : ContDiffAt ℝ 2 f y) :
    fderiv ℝ (fderiv ℝ f) y u v =
      fderiv ℝ (fderiv ℝ f) y v u :=
  (hf.isSymmSndFDerivAt (by simp)).eq u v

end QuaternionicSymmetry.GeneralImmersionHessianSymmetry
