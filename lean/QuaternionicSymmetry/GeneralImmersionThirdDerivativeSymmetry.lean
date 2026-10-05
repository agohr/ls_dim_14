import QuaternionicSymmetry.GeneralImmersionGaussJet
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The actual third Fréchet derivative of a C³ immersion is symmetric
in the two base directions needed for curvature antisymmetrization. -/

namespace QuaternionicSymmetry.GeneralImmersionThirdDerivativeSymmetry

open scoped ContDiff

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem third_derivative_swap_first_two
    (f : E → V) (y u v w : E) (hf : ContDiffAt ℝ 3 f y) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y v u w := by
  have hdF : ContDiffAt ℝ 2 (fderiv ℝ f) y :=
    hf.fderiv_right (m := 2) (by norm_num)
  have h := (hdF.isSymmSndFDerivAt (by simp)).eq u v
  exact congrArg (fun L : E →L[ℝ] V => L w) h

end QuaternionicSymmetry.GeneralImmersionThirdDerivativeSymmetry
