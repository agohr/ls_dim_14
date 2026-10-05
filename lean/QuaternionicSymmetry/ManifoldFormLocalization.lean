import QuaternionicSymmetry.ManifoldDifferentialForms
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Multiplication of genuine tangent forms by smooth scalar functions.
This is the localization operation used with partitions of unity. -/
namespace QuaternionicSymmetry.ManifoldFormLocalization

open ManifoldDifferentialForms
open scoped Manifold ContDiff Topology
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

noncomputable def scalarMultiply (f : M → ℝ) (α : Form 𝓘(ℝ, E) M n) : Form 𝓘(ℝ, E) M n :=
  fun x => f x • α x

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem inChartModel_scalarMultiply (f : M → ℝ) (α : Form 𝓘(ℝ, E) M n) (p : M) :
    inChartModel p (scalarMultiply f α) =
      fun y => f ((extChartAt 𝓘(ℝ, E) p).symm y) • inChartModel p α y := by
  ext y v
  rfl

theorem scalarMultiply_smooth (f : M → ℝ) (α : Form 𝓘(ℝ, E) M n)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hα : ChartSmooth α) :
    ChartSmooth (scalarMultiply f α) := by
  intro p
  rw [inChartModel_scalarMultiply]
  have hfc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y => f ((extChartAt 𝓘(ℝ, E) p).symm y))
      (extChartAt 𝓘(ℝ, E) p).target :=
    hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)
  exact hfc.contDiffOn.smul (hα p)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem finite_sum_scalarMultiply {ι : Type*} (s : Finset ι) (f : ι → M → ℝ)
    (α : Form 𝓘(ℝ, E) M n) (hf : ∀ x, ∑ i ∈ s, f i x = 1) :
    ∑ i ∈ s, scalarMultiply (f i) α = α := by
  classical
  funext x
  simp only [Finset.sum_apply, scalarMultiply, ← Finset.sum_smul, hf, one_smul]

end QuaternionicSymmetry.ManifoldFormLocalization
