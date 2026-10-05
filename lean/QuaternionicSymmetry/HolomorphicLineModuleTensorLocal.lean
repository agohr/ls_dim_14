import QuaternionicSymmetry.HolomorphicLineModuleTensorPairing
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! On an open subset of a simultaneous line chart, the actual tensor
pairing is an isomorphism of modules over holomorphic functions. This
local statement is the input to sheafification, not a false claim about
tensor products of global section modules. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleTensorLocal

open CategoryTheory TopologicalSpace Manifold
open HolomorphicLineModuleSheaf HolomorphicLineModuleLocalFree
open HolomorphicLineTensor HolomorphicLineModuleTensorPairing
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

def localTensorEquiv (i : ι) (a : κ) (U : Opens B)
    (hZ : (U : Set B) ⊆ Z.baseSet i) (hW : (U : Set B) ⊆ W.baseSet a) :
    (sectionSubmodule IB Z U ⊗[Functions IB U] sectionSubmodule IB W U) ≃ₗ[Functions IB U]
      sectionSubmodule IB (tensorCore Z W) U :=
  ((TensorProduct.congr (coordinateLinearEquiv IB Z i U hZ)
      (coordinateLinearEquiv IB W a U hW)).trans
    (TensorProduct.lid (Functions IB U) (Functions IB U))).trans
      (coordinateLinearEquiv IB (tensorCore Z W) (i, a) U
        (fun _ hx => ⟨hZ hx, hW hx⟩)).symm

theorem localTensorEquiv_tmul (i : ι) (a : κ) (U : Opens B)
    (hZ : (U : Set B) ⊆ Z.baseSet i) (hW : (U : Set B) ⊆ W.baseSet a)
    (s : sectionSubmodule IB Z U) (t : sectionSubmodule IB W U) :
    localTensorEquiv IB Z W i a U hZ hW (s ⊗ₜ[Functions IB U] t) =
      sectionProduct IB Z W s t := by
  let c := coordinateLinearEquiv IB (tensorCore Z W) (i, a) U
    (fun _ hx => ⟨hZ hx, hW hx⟩)
  change c.symm (coordinateLinearEquiv IB Z i U hZ s *
    coordinateLinearEquiv IB W a U hW t) = _
  apply c.injective
  rw [c.apply_symm_apply]
  apply Subtype.ext
  funext x
  exact (coefficient_product Z W (i, a) s.1 t.1 x).symm

theorem tensorMap_eq_localTensorEquiv (i : ι) (a : κ) (U : Opens B)
    (hZ : (U : Set B) ⊆ Z.baseSet i) (hW : (U : Set B) ⊆ W.baseSet a) :
    tensorMap IB Z W U = (localTensorEquiv IB Z W i a U hZ hW).toLinearMap := by
  apply TensorProduct.ext'
  intro s t
  exact (localTensorEquiv_tmul IB Z W i a U hZ hW s t).symm

/-- The actual pairing is bijective on every smaller simultaneous chart. -/
theorem tensorMap_bijective_of_le (i : ι) (a : κ) (U : Opens B)
    (hZ : (U : Set B) ⊆ Z.baseSet i) (hW : (U : Set B) ⊆ W.baseSet a) :
    Function.Bijective (tensorMap IB Z W U) := by
  rw [tensorMap_eq_localTensorEquiv IB Z W i a U hZ hW]
  exact (localTensorEquiv IB Z W i a U hZ hW).bijective

end
end QuaternionicSymmetry.HolomorphicLineModuleTensorLocal
