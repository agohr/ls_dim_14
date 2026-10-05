import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation under a real interval integral with a complex Banach
parameter. The existing dominated derivative theorem applies unchanged. -/
namespace QuaternionicSymmetry.ComplexParametricIntervalIntegral
open MeasureTheory Set Filter Metric
open scoped Topology Interval
noncomputable section
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem hasFDerivAt_intervalIntegral
    {F : H → ℝ → E} {F' : H → ℝ → H →L[ℂ] E} {x : H} {s : Set H}
    {a b : ℝ} {bound : ℝ → ℝ} (hs : s ∈ 𝓝 x)
    (hF : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (volume.restrict (Ι a b)))
    (hFi : IntervalIntegrable (F x) volume a b)
    (hF' : AEStronglyMeasurable (F' x) (volume.restrict (Ι a b)))
    (hb : ∀ᵐ t ∂volume.restrict (Ι a b), ∀ y ∈ s, ‖F' y t‖ ≤ bound t)
    (hbi : IntervalIntegrable bound volume a b)
    (hd : ∀ᵐ t ∂volume.restrict (Ι a b), ∀ y ∈ s, HasFDerivAt (F · t) (F' y t) y) :
    HasFDerivAt (fun y => ∫ t in a..b, F y t) (∫ t in a..b, F' x t) x := by
  rw [ae_restrict_uIoc_iff] at hd hb
  simp_rw [AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff,eventually_and] at hF hF'
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF.1 hFi.1 hF'.1 hb.1 hbi.1 hd.1).sub
    (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF.2 hFi.2 hF'.2 hb.2 hbi.2 hd.2)

/-- A useful form with continuous time dependence and a constant bound. -/
theorem hasFDerivAt_intervalIntegral_of_continuous
    {F : H → ℝ → E} {F' : H → ℝ → H →L[ℂ] E} {x : H} {s : Set H}
    {a b B : ℝ} (hs : s ∈ 𝓝 x)
    (hF : ∀ y ∈ s, ContinuousOn (F y) (uIcc a b))
    (hF' : ContinuousOn (F' x) (uIcc a b))
    (hb : ∀ t ∈ uIcc a b, ∀ y ∈ s, ‖F' y t‖ ≤ B)
    (hd : ∀ t ∈ uIcc a b, ∀ y ∈ s, HasFDerivAt (F · t) (F' y t) y) :
    HasFDerivAt (fun y => ∫ t in a..b, F y t) (∫ t in a..b, F' x t) x := by
  apply hasFDerivAt_intervalIntegral hs
  · filter_upwards [hs] with y hy
    exact ((hF y hy).aestronglyMeasurable measurableSet_uIcc).mono_set uIoc_subset_uIcc
  · exact (hF x (mem_of_mem_nhds hs)).intervalIntegrable
  · exact (hF'.aestronglyMeasurable measurableSet_uIcc).mono_set uIoc_subset_uIcc
  · exact (ae_restrict_mem measurableSet_uIoc).mono fun t ht => hb t (uIoc_subset_uIcc ht)
  · exact intervalIntegrable_const
  · exact (ae_restrict_mem measurableSet_uIoc).mono fun t ht => hd t (uIoc_subset_uIcc ht)

end
end QuaternionicSymmetry.ComplexParametricIntervalIntegral
