import QuaternionicSymmetry.ExteriorDuality
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic

/-! Transport of coordinate covectors into the dual of a finite-dimensional
vector space, and the induced map on the actual exterior algebra. -/

namespace QuaternionicSymmetry.ExteriorCovectorTransport

open Module
open scoped BigOperators

noncomputable section

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module ℝ V]

/-- The covector whose coordinates are the finite linear combination of the
basis coordinate covectors. -/
def covectorMap (b : Basis ι ℝ V) :
    (ι → ℝ) →ₗ[ℝ] Module.Dual ℝ V where
  toFun x := ∑ i, x i • b.coord i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Pi.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul]

omit [DecidableEq ι] in
@[simp] theorem covectorMap_apply (b : Basis ι ℝ V) (x : ι → ℝ) :
    covectorMap b x = ∑ i, x i • b.coord i := rfl

theorem covectorMap_eq_dualBasis (b : Basis ι ℝ V) :
    covectorMap b = b.dualBasis.equivFun.symm := by
  ext x v
  simp [covectorMap, Basis.equivFun_symm_apply, Basis.coe_dualBasis]

/-- The coordinate covector map is the linear equivalence induced by the dual
basis. -/
noncomputable def covectorEquiv (b : Basis ι ℝ V) :
    (ι → ℝ) ≃ₗ[ℝ] Module.Dual ℝ V := b.dualBasis.equivFun.symm

@[simp] theorem covectorEquiv_apply (b : Basis ι ℝ V) (x : ι → ℝ) :
    covectorEquiv b x = covectorMap b x := by
  exact congrArg (fun f : (ι → ℝ) →ₗ[ℝ] Module.Dual ℝ V => f x)
    (covectorMap_eq_dualBasis b).symm

@[simp] theorem covectorMap_single (b : Basis ι ℝ V) (i : ι) :
    covectorMap b (Pi.single i 1) = b.coord i := by
  rw [← covectorEquiv_apply]
  simp [covectorEquiv, Basis.coe_dualBasis]

/-- The induced algebra homomorphism on the actual exterior algebras. -/
def exteriorCovectorMap (b : Basis ι ℝ V) :
    ExteriorAlgebra ℝ (ι → ℝ) →ₐ[ℝ]
      ExteriorAlgebra ℝ (Module.Dual ℝ V) :=
  ExteriorAlgebra.map (covectorMap b)

omit [DecidableEq ι] in
@[simp] theorem exteriorCovectorMap_ι (b : Basis ι ℝ V) (x : ι → ℝ) :
    exteriorCovectorMap b (ExteriorAlgebra.ι ℝ x) =
      ExteriorAlgebra.ι ℝ (covectorMap b x) := by
  rw [exteriorCovectorMap, ExteriorAlgebra.map_apply_ι]

@[simp] theorem exteriorCovectorMap_coordinate (b : Basis ι ℝ V) (i : ι) :
    exteriorCovectorMap b (ExteriorAlgebra.ι ℝ (Pi.single i 1)) =
      ExteriorAlgebra.ι ℝ (b.coord i) := by
  rw [exteriorCovectorMap_ι, covectorMap_single]

end
end QuaternionicSymmetry.ExteriorCovectorTransport
