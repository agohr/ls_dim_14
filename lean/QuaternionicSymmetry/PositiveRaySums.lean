import QuaternionicSymmetry.PositiveRay
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace QuaternionicSymmetry.PositiveRay
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem sum {ι : Type*} [Fintype ι] {v : V} {f : ι → V}
    (h : ∀ i, Contains v (f i)) : Contains v (∑ i, f i) := by
  choose r hr he using h
  refine ⟨∑ i, r i, Finset.sum_nonneg (fun i _ => hr i), ?_⟩
  simp only [he, Finset.sum_smul]

end QuaternionicSymmetry.PositiveRay
