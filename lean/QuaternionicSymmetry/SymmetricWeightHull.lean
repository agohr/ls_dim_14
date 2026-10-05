import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.NormNum

/-! The convex step in the nonvanishing of extremal contact weights.
Actual antipodal weight symmetry and existence of a nonzero geometric
weight remain separate obligations. No fixed-point or weight data is
invented here, and full-dimensionality is not needed for this step. -/

namespace QuaternionicSymmetry.SymmetricWeightHull

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A set containing a nonzero vector and its negative cannot have zero
as an extreme point. Convexity of the set is not required. -/
theorem zero_not_extreme_of_opposite_pair {s : Set E} {w : E}
    (hw : w ∈ s) (hneg : -w ∈ s) (hne : w ≠ 0) :
    (0 : E) ∉ s.extremePoints ℝ := by
  intro hzero
  have hsegment : (0 : E) ∈ openSegment ℝ w (-w) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num,
      by norm_num, ?_⟩
    simp
  exact hne (hzero.2 hw hneg hsegment)

/-- For a symmetric set of weights containing a nonzero weight, every
extreme point of its actual convex hull is nonzero. -/
theorem extreme_ne_zero {weights : Set E}
    (hneg : ∀ w ∈ weights, -w ∈ weights)
    (hne : ∃ w ∈ weights, w ≠ 0) {v : E}
    (hv : v ∈ (convexHull ℝ weights).extremePoints ℝ) : v ≠ 0 := by
  obtain ⟨w, hw, hwne⟩ := hne
  intro hvzero
  subst v
  exact zero_not_extreme_of_opposite_pair
    (subset_convexHull ℝ weights hw)
    (subset_convexHull ℝ weights (hneg w hw)) hwne hv

/-- A vertex of the convex hull is an actual weight, not merely a convex
combination. This applies to any indexed weight family. -/
theorem extreme_is_weight {ι : Type*} (weight : ι → E) {v : E}
    (hv : v ∈ (convexHull ℝ (Set.range weight)).extremePoints ℝ) :
    ∃ i, weight i = v := by
  have h : v ∈ Set.range weight := extremePoints_convexHull_subset hv
  exact h

/-- Interface for the genuine geometric antipodal map: once its action
negates the actual weights and one actual weight is nonzero, all extremal
weights are nonzero. No finiteness or full-span premise is necessary. -/
theorem extreme_ne_zero_of_antipodal {ι : Type*}
    (weight : ι → E) (antipodal : ι → ι)
    (hneg : ∀ i, weight (antipodal i) = -weight i)
    (hne : ∃ i, weight i ≠ 0) {v : E}
    (hv : v ∈ (convexHull ℝ (Set.range weight)).extremePoints ℝ) : v ≠ 0 := by
  apply extreme_ne_zero (weights := Set.range weight) ?_ ?_ hv
  · rintro w ⟨i, rfl⟩
    exact ⟨antipodal i, hneg i⟩
  · obtain ⟨i, hi⟩ := hne
    exact ⟨weight i, ⟨i, rfl⟩, hi⟩

/-- Full affine span in a nontrivial weight space supplies a nonzero
weight. This is pure affine algebra, not a torus-action theorem. -/
theorem exists_nonzero_of_affineSpan_eq_top [Nontrivial E]
    {weights : Set E} (hspan : affineSpan ℝ weights = ⊤) :
    ∃ w ∈ weights, w ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ w ∈ weights, w = 0 := by
    intro w hw
    by_contra hne
    exact h ⟨w, hw, hne⟩
  have hsub : weights ⊆ ({0} : Set E) := fun w hw => hz w hw
  have hle := affineSpan_mono ℝ hsub
  rw [hspan] at hle
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  have hmem : w ∈ affineSpan ℝ ({0} : Set E) := hle (by simp)
  exact hw (by simpa only [AffineSubspace.mem_affineSpan_singleton] using hmem)

/-- The source-facing polytope argument: central symmetry together with
full affine span implies that every extreme point is nonzero. The geometric
verification of both hypotheses is deliberately not part of this lemma. -/
theorem extreme_ne_zero_of_full_affine_span [Nontrivial E]
    {weights : Set E} (hneg : ∀ w ∈ weights, -w ∈ weights)
    (hspan : affineSpan ℝ weights = ⊤) {v : E}
    (hv : v ∈ (convexHull ℝ weights).extremePoints ℝ) : v ≠ 0 :=
  extreme_ne_zero hneg (exists_nonzero_of_affineSpan_eq_top hspan) hv

end QuaternionicSymmetry.SymmetricWeightHull
