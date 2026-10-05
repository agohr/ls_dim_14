import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Clopen

/-! An identity theorem for sets locally cut out by one holomorphic scalar
function.  Local defining functions may differ, so the theorem applies to
zeros of a line-bundle section without choosing a global trivialization. -/

namespace QuaternionicSymmetry.ComplexLocallyAnalyticZeroSet

open Set Filter
open scoped Topology

/-- The zero set has a scalar analytic defining function near every point.
No agreement of the defining functions on overlaps is required. -/
def LocallyAnalyticZeroSet (S : Set ℂ) : Prop :=
  ∀ z : ℂ, ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧
    ∀ᶠ w in 𝓝 z, (w ∈ S ↔ f w = 0)

/-- Accumulating zeros force a whole neighborhood of zeros. -/
theorem mem_nhds_of_frequently {S : Set ℂ} (hS : LocallyAnalyticZeroSet S)
    {z : ℂ} (hz : ∃ᶠ w in 𝓝[≠] z, w ∈ S) : S ∈ 𝓝 z := by
  obtain ⟨f, hf, hzero⟩ := hS z
  have hfreq : ∃ᶠ w in 𝓝[≠] z, f w = 0 := by
    exact (hz.and_eventually (hzero.filter_mono nhdsWithin_le_nhds)).mono
      (fun w hw => hw.2.mp hw.1)
  have hevent := hf.frequently_zero_iff_eventually_zero.mp hfreq
  filter_upwards [hevent, hzero] with w hw hiff
  exact hiff.mpr hw

/-- The interior of a locally analytic zero set is closed as well as open. -/
theorem isClosed_interior {S : Set ℂ} (hS : LocallyAnalyticZeroSet S) :
    IsClosed (interior S) := by
  apply closure_subset_iff_isClosed.mp
  intro z hz
  by_cases hi : z ∈ interior S
  · exact hi
  have hsub : interior S ⊆ S \ {z} := by
    intro w hw
    refine ⟨interior_subset hw, ?_⟩
    intro heq
    exact hi (by simpa only [mem_singleton_iff.mp heq] using hw)
  have hfreq : ∃ᶠ w in 𝓝[≠] z, w ∈ S :=
    mem_closure_ne_iff_frequently_within.mp (closure_mono hsub hz)
  exact mem_interior_iff_mem_nhds.mpr (mem_nhds_of_frequently hS hfreq)

/-- A locally analytic zero set in the complex plane with an accumulation
point is the entire plane.  In particular, this does not assume one global
scalar function whose zero set is `S`. -/
theorem eq_univ_of_frequently {S : Set ℂ} (hS : LocallyAnalyticZeroSet S)
    {z : ℂ} (hz : ∃ᶠ w in 𝓝[≠] z, w ∈ S) : S = univ := by
  have hi : z ∈ interior S :=
    mem_interior_iff_mem_nhds.mpr (mem_nhds_of_frequently hS hz)
  have hclopen : IsClopen (interior S) := ⟨isClosed_interior hS, isOpen_interior⟩
  have hall : interior S = univ := hclopen.eq_univ ⟨z, hi⟩
  exact univ_subset_iff.mp (hall ▸ interior_subset)

end QuaternionicSymmetry.ComplexLocallyAnalyticZeroSet
