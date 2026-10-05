import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-! A fixed continuous linear map on coefficients commutes with the actual
exterior derivative, in every form degree. -/

namespace QuaternionicSymmetry.DifferentialFormCoefficient

open ContinuousAlternatingMap

noncomputable section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n : ℕ}

def mapForm (L : F →L[ℝ] G) (ω : E → E [⋀^Fin n]→L[ℝ] F) :
    E → E [⋀^Fin n]→L[ℝ] G := fun x => L.compContinuousAlternatingMap (ω x)

theorem mapForm_apply (L : F →L[ℝ] G) (ω : E → E [⋀^Fin n]→L[ℝ] F)
    (x : E) (v : Fin n → E) : mapForm L ω x v = L (ω x v) := rfl

theorem differentiableAt_mapForm (L : F →L[ℝ] G) (ω : E → E [⋀^Fin n]→L[ℝ] F)
    (x : E) (hω : DifferentiableAt ℝ ω x) : DifferentiableAt ℝ (mapForm L ω) x :=
  ((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E F G) L).differentiableAt.comp x hω

theorem contDiffAt_mapForm (L : F →L[ℝ] G) (ω : E → E [⋀^Fin n]→L[ℝ] F)
    (x : E) {r : WithTop ℕ∞} (hω : ContDiffAt ℝ r ω x) :
    ContDiffAt ℝ r (mapForm L ω) x := by
  exact ((ContinuousLinearMap.compContinuousAlternatingMapCLM (ι := Fin n) ℝ E F G) L).contDiff.contDiffAt.comp x hω

theorem extDeriv_mapForm (L : F →L[ℝ] G) (ω : E → E [⋀^Fin n]→L[ℝ] F)
    (x : E) (hω : DifferentiableAt ℝ ω x) :
    extDeriv (mapForm L ω) x = L.compContinuousAlternatingMap (extDeriv ω x) := by
  have hd := (((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E F G) L).hasFDerivAt.comp
    x hω.hasFDerivAt).fderiv
  change fderiv ℝ (mapForm L ω) x = _ at hd
  rw [extDeriv, hd]
  ext v
  simp [extDeriv, alternatizeUncurryFin_apply, _root_.map_sum]

end
end QuaternionicSymmetry.DifferentialFormCoefficient
