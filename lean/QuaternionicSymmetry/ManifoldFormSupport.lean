import QuaternionicSymmetry.ManifoldFormLocalization
import QuaternionicSymmetry.ManifoldDeRhamWedge

/-! Support control for exterior differentiation and localization of genuine
tangent forms. No smoothness premise is needed for locality. -/
namespace QuaternionicSymmetry.ManifoldFormSupport

open Filter Set ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldFormLocalization
open scoped Manifold ContDiff Topology
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {n : ℕ}

def support (α : Form 𝓘(ℝ, E) M n) : Set M := {x | α x ≠ 0}
def tsupport (α : Form 𝓘(ℝ, E) M n) : Set M := closure (support α)

theorem derivative_zero_of_eventually_zero (α : Form 𝓘(ℝ, E) M n) (x : M)
    (hz : ∀ᶠ y in 𝓝 x, α y = 0) : exteriorDerivative α x = 0 := by
  have hs : Tendsto (extChartAt 𝓘(ℝ, E) x).symm
      (𝓝 (extChartAt 𝓘(ℝ, E) x x)) (𝓝 x) := by
    have h := continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) x
    change Tendsto _ _ (𝓝 ((extChartAt 𝓘(ℝ, E) x).symm (extChartAt 𝓘(ℝ, E) x x))) at h
    simpa only [(extChartAt 𝓘(ℝ, E) x).left_inv (mem_extChartAt_source x)] using h
  have he : inChartModel x α =ᶠ[𝓝 (extChartAt 𝓘(ℝ, E) x x)] 0 := by
    filter_upwards [hs.eventually hz] with y hy
    ext v
    rw [inChartModel_apply, hy]
    rfl
  have hd : extDeriv (inChartModel x α) (extChartAt 𝓘(ℝ, E) x x) = 0 := by
    rw [he.extDeriv_eq]
    ext v
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  unfold exteriorDerivative
  rw [hd]
  ext v
  rfl

theorem support_derivative_subset (α : Form 𝓘(ℝ, E) M n) :
    support (exteriorDerivative α) ⊆ tsupport α := by
  intro x hx
  by_contra hxt
  have hn : (tsupport α)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hxt
  apply hx
  apply derivative_zero_of_eventually_zero α x
  filter_upwards [hn] with y hy
  by_contra ha
  exact hy (subset_closure ha)

theorem tsupport_scalarMultiply_subset (f : M → ℝ) (α : Form 𝓘(ℝ, E) M n) :
    tsupport (scalarMultiply f α) ⊆ _root_.tsupport f := by
  apply closure_mono
  intro x hx
  change f x ≠ 0
  intro hf
  exact hx (by simp [scalarMultiply, hf])

theorem support_castForm_subset {m : ℕ} (h : n = m) (α : Form 𝓘(ℝ, E) M n) :
    support (castForm h α) ⊆ support α := by
  cases h
  exact Set.Subset.rfl

end QuaternionicSymmetry.ManifoldFormSupport
