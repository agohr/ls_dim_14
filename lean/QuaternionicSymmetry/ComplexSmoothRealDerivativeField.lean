import QuaternionicSymmetry.ComplexSmoothRealHessianLocal

/-! The real derivative field of a real-smooth holomorphic map is itself
complex-differentiable, as a map into the complex Banach space of real-linear
operators. This is an intermediate step for higher regularity. -/

namespace QuaternionicSymmetry.ComplexSmoothRealDerivativeField

open scoped ContDiff
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

def complexifyCommutingMap
    (L : E →L[ℝ] G)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) : E →L[ℂ] G where
  toFun := L
  map_add' := L.map_add
  map_smul' := by
    intro c v
    change L (c • v) = c • L v
    conv_lhs => rw [← Complex.re_add_im c]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [add_smul, L.map_add, mul_smul, Complex.coe_smul,
      L.map_smul, hI]
  cont := L.continuous

theorem complexifyCommutingMap_restrictScalars
    (L : E →L[ℝ] G)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    (complexifyCommutingMap L hI).restrictScalars ℝ = L := by
  ext v
  rfl

/-- The real derivative field of a holomorphic real-C∞ map is holomorphic
on every open chart domain. Its values remain real-linear operators; a
separate range-transfer step is needed for the complex derivative field. -/
theorem realDerivativeField_differentiableOn_complex
    {f : E → F} {s : Set E} (hs : IsOpen s)
    (hReal : ContDiffOn ℝ ∞ f s)
    (hComplex : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fderiv ℝ f) s := by
  have hRealDeriv : ContDiffOn ℝ ∞ (fderiv ℝ f) s :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hReal).2
  intro x hx
  have hRealAt : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hRealDeriv.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hI (w : E) :
      (fderiv ℝ (fderiv ℝ f) x) (Complex.I • w) =
        Complex.I • (fderiv ℝ (fderiv ℝ f) x) w := by
    ext v
    exact ComplexSmoothRealHessianLocal.real_hessian_commutes_i_outer_on
      hs hReal hComplex hx v w
  exact ((differentiableAt_iff_restrictScalars ℝ hRealAt).2
    ⟨complexifyCommutingMap (fderiv ℝ (fderiv ℝ f) x) hI,
      complexifyCommutingMap_restrictScalars _ hI⟩).differentiableWithinAt

end
end QuaternionicSymmetry.ComplexSmoothRealDerivativeField
