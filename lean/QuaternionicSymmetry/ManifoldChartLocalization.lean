import QuaternionicSymmetry.ManifoldFormLocalization
import QuaternionicSymmetry.CompactSupportDomainStokes

/-! Zero extension of a chart-supported localized tangent form. -/
namespace QuaternionicSymmetry.ManifoldChartLocalization

open Set Filter ManifoldDifferentialForms ManifoldFormLocalization
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

def localizedChartForm (p : M) (f : M → ℝ) (α : Form 𝓘(ℝ, E) M n) :
    E → E [⋀^Fin n]→L[ℝ] ℝ :=
  (extChartAt 𝓘(ℝ, E) p).target.indicator (inChartModel p (scalarMultiply f α))

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem localizedChartForm_eq (p : M) (f : M → ℝ) (α : Form 𝓘(ℝ, E) M n)
    {y : E} (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    localizedChartForm p f α y = inChartModel p (scalarMultiply f α) y :=
  Set.indicator_of_mem hy _

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem support_localizedChartForm_subset (p : M) (f : M → ℝ)
    (α : Form 𝓘(ℝ, E) M n) :
    Function.support (localizedChartForm p f α) ⊆
      (extChartAt 𝓘(ℝ, E) p) '' tsupport f := by
  intro y hy
  have hyt : y ∈ (extChartAt 𝓘(ℝ, E) p).target := by
    by_contra ht
    exact hy (Set.indicator_of_notMem ht _)
  have hf : f ((extChartAt 𝓘(ℝ, E) p).symm y) ≠ 0 := by
    intro hf
    apply hy
    simp only [localizedChartForm_eq p f α hyt, inChartModel_scalarMultiply, hf, zero_smul]
  exact ⟨(extChartAt 𝓘(ℝ, E) p).symm y,
    subset_tsupport f hf, (extChartAt 𝓘(ℝ, E) p).right_inv hyt⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem localizedChartForm_compactSupport (p : M) (f : M → ℝ)
    (α : Form 𝓘(ℝ, E) M n) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ (extChartAt 𝓘(ℝ, E) p).source) :
    HasCompactSupport (localizedChartForm p f α) := by
  have hi := hc.image_of_continuousOn ((continuousOn_extChartAt p).mono hsub)
  exact hi.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (support_localizedChartForm_subset p f α) hi.isClosed)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem tsupport_localizedChartForm_subset (p : M) (f : M → ℝ)
    (α : Form 𝓘(ℝ, E) M n) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ (extChartAt 𝓘(ℝ, E) p).source) :
    tsupport (localizedChartForm p f α) ⊆ (extChartAt 𝓘(ℝ, E) p).target := by
  have hi := hc.image_of_continuousOn ((continuousOn_extChartAt p).mono hsub)
  apply (closure_minimal (support_localizedChartForm_subset p f α) hi.isClosed).trans
  rintro y ⟨x, hx, rfl⟩
  exact (extChartAt 𝓘(ℝ, E) p).map_source (hsub hx)

theorem localizedChartForm_smooth (p : M) (f : M → ℝ)
    (α : Form 𝓘(ℝ, E) M n) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ (extChartAt 𝓘(ℝ, E) p).source)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hα : ChartSmooth α) :
    ContDiff ℝ ∞ (localizedChartForm p f α) := by
  apply CompactSupportDomainStokes.contDiff_of_tsupport_subset
    (isOpen_extChartAt_target p) _ (tsupport_localizedChartForm_subset p f α hc hsub)
  exact (scalarMultiply_smooth f α hf hα p).congr
    (fun y hy => localizedChartForm_eq p f α hy)

end
end QuaternionicSymmetry.ManifoldChartLocalization
