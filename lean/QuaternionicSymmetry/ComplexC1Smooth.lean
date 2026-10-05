import QuaternionicSymmetry.ComplexC1DerivativeRegularity

/-! Complex C1 maps on finite-dimensional complex domains are smooth. The
proof repeatedly applies the internally checked Cauchy-integral bootstrap. -/
namespace QuaternionicSymmetry.ComplexC1Smooth
open scoped ContDiff
noncomputable section
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem contDiffOn_nat_of_one (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
      {f : E → F} {U : Set E}, IsOpen U → ContDiffOn ℂ 1 f U → ContDiffOn ℂ n f U := by
  induction n with
  | zero =>
    intro F _ _ _ f U hU hf
    exact contDiffOn_zero.mpr hf.continuousOn
  | succ n ih =>
    intro F _ _ _ f U hU hf
    rw [Nat.cast_succ]
    apply (contDiffOn_succ_iff_fderiv_of_isOpen hU).2
    refine ⟨hf.differentiableOn_one,by simp,?_⟩
    exact ih hU (ComplexC1DerivativeRegularity.fderiv_contDiffOn_one hU hf)

theorem contDiffOn_infty_of_one {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℂ 1 f U) :
    ContDiffOn ℂ ∞ f U :=
  contDiffOn_infty.mpr (fun n => contDiffOn_nat_of_one n hU hf)

end
end QuaternionicSymmetry.ComplexC1Smooth
