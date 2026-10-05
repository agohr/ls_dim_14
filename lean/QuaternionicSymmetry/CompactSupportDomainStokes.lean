import QuaternionicSymmetry.CompactSupportLocalStokes

/-! Local Stokes on an open coordinate domain, for forms supported away from
its boundary. Smoothness outside the domain is derived from vanishing. -/
namespace QuaternionicSymmetry.CompactSupportDomainStokes

open MeasureTheory Measure Set Filter
open scoped ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_of_tsupport_subset {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f s) (hsub : tsupport f ⊆ s) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact (hf x hx).contDiffAt (hs.mem_nhds hx)
  · have hz : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hx' => hx (hsub hx'))
    exact contDiffAt_const.congr_of_eventuallyEq hz

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

theorem integral_extDeriv_eq_zero {n : ℕ} {s : Set E} (hs : IsOpen s)
    {α : E → E [⋀^Fin n]→L[ℝ] ℝ}
    (hα : ContDiffOn ℝ ∞ α s) (hc : HasCompactSupport α)
    (hsub : tsupport α ⊆ s) (v : Fin (n + 1) → E) :
    (∫ x, extDeriv α x v ∂μ) = 0 :=
  CompactSupportLocalStokes.integral_extDeriv_eq_zero
    (contDiff_of_tsupport_subset hs hα hsub) hc v

theorem setIntegral_extDeriv_eq_zero {n : ℕ} {s : Set E} (hs : IsOpen s)
    {α : E → E [⋀^Fin n]→L[ℝ] ℝ}
    (hα : ContDiffOn ℝ ∞ α s) (hc : HasCompactSupport α)
    (hsub : tsupport α ⊆ s) (v : Fin (n + 1) → E) :
    (∫ x in s, extDeriv α x v ∂μ) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_extDeriv_eq_zero hs hα hc hsub v
  · intro x hx
    have hz : α =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hx' => hx (hsub hx'))
    simp [extDeriv, hz.fderiv_eq,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply]

end QuaternionicSymmetry.CompactSupportDomainStokes
