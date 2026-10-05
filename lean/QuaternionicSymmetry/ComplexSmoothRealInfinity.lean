import QuaternionicSymmetry.ComplexSmoothRealProjection

/-! Local real-C∞ plus complex differentiability upgrades to complex-C∞
for finite-dimensional complex model spaces. The open-domain version applies
directly to manifold extended charts. -/

namespace QuaternionicSymmetry.ComplexSmoothRealInfinity

open scoped ContDiff
open ComplexSmoothRealDerivativeField ComplexSmoothRealProjection
noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

private theorem contDiffOn_nat_of_real_complex (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]
      [FiniteDimensional ℂ F] {f : E → F} {s : Set E},
      IsOpen s → ContDiffOn ℝ ∞ f s → DifferentiableOn ℂ f s →
        ContDiffOn ℂ n f s := by
  induction n with
  | zero =>
      intro F _ _ _ f s hs hReal hComplex
      exact contDiffOn_zero.mpr hComplex.continuousOn
  | succ n ih =>
      intro F _ _ _ f s hs hReal hComplex
      have hRealDeriv : ContDiffOn ℝ ∞ (fderiv ℝ f) s :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hReal).2
      have hComplexRealDeriv : DifferentiableOn ℂ (fderiv ℝ f) s :=
        realDerivativeField_differentiableOn_complex hs hReal hComplex
      let P : (E →L[ℝ] F) →L[ℂ] (E →L[ℂ] F) := complexProjection
      have hEq : Set.EqOn (fderiv ℂ f)
          (fun x => P (fderiv ℝ f x)) s := by
        intro x hx
        have hd := ((hComplex x hx).differentiableAt (hs.mem_nhds hx)).fderiv_restrictScalars ℝ
        change fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ at hd
        calc
          fderiv ℂ f x = complexProjectionValue ((fderiv ℂ f x).restrictScalars ℝ) :=
            (complexProjectionValue_of_complex _).symm
          _ = P (fderiv ℝ f x) := by rw [hd]; rfl
      have hRealProjected : ContDiffOn ℝ ∞ (fun x => P (fderiv ℝ f x)) s :=
        ((P.restrictScalars ℝ).contDiff.contDiffOn (s := Set.univ)).comp hRealDeriv
          (by intro x hx; exact Set.mem_univ _)
      have hComplexProjected : DifferentiableOn ℂ
          (fun x => P (fderiv ℝ f x)) s :=
        (P.differentiable.differentiableOn (s := Set.univ)).comp
          hComplexRealDeriv (by intro x hx; exact Set.mem_univ _)
      have hRealComplexDeriv : ContDiffOn ℝ ∞ (fderiv ℂ f) s :=
        hRealProjected.congr hEq
      have hComplexDeriv : DifferentiableOn ℂ (fderiv ℂ f) s :=
        hComplexProjected.congr hEq
      exact (contDiffOn_succ_iff_fderiv_of_isOpen hs).2
        ⟨hComplex, by simp, ih hs hRealComplexDeriv hComplexDeriv⟩

/-- A real-C∞ map that is complex-differentiable on an open set is complex-C∞
there, with no assumptions outside the open set. -/
theorem contDiffOn_infty_of_real_complex
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {f : E → F} {s : Set E}
    (hs : IsOpen s) (hReal : ContDiffOn ℝ ∞ f s)
    (hComplex : DifferentiableOn ℂ f s) : ContDiffOn ℂ ∞ f s := by
  exact contDiffOn_infty.mpr
    (fun n => contDiffOn_nat_of_real_complex n hs hReal hComplex)

end
end QuaternionicSymmetry.ComplexSmoothRealInfinity
