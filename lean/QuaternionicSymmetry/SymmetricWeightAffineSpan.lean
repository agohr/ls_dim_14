import QuaternionicSymmetry.SymmetricWeightHull
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-! Antipodal symmetry turns literal linear span into affine span. -/
namespace QuaternionicSymmetry.SymmetricWeightAffineSpan

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

 theorem affineSpan_eq_top_of_symmetric_span
    {W : Set V} (hNonempty : W.Nonempty)
    (hNeg : ∀ w ∈ W, -w ∈ W)
    (hSpan : Submodule.span ℝ W = ⊤) : affineSpan ℝ W = ⊤ := by
  obtain ⟨w,hw⟩ := hNonempty
  have hwA := subset_affineSpan ℝ W hw
  have hnA := subset_affineSpan ℝ W (hNeg w hw)
  have hZero : (0 : V) ∈ affineSpan ℝ W := by
    have hm := AffineMap.lineMap_mem (1 / 2 : ℝ) hwA hnA
    rw [AffineMap.lineMap_apply_module] at hm
    norm_num at hm
    simpa using hm
  have hInsert : affineSpan ℝ (insert 0 W) = affineSpan ℝ W := by
    apply le_antisymm
    · exact affineSpan_le.mpr (by
        intro x hx
        rcases hx with rfl | hx
        · exact hZero
        · exact subset_affineSpan ℝ W hx)
    · exact affineSpan_mono ℝ (Set.subset_insert 0 W)
  apply SetLike.coe_injective
  rw [← hInsert, affineSpan_insert_zero, hSpan]
  rfl

end QuaternionicSymmetry.SymmetricWeightAffineSpan
