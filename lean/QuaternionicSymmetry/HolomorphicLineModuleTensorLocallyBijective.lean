import QuaternionicSymmetry.HolomorphicLineModuleTensorPresheaf
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! The canonical morphism from the actual tensor presheaf to tensor-line
sections is locally bijective for the genuine topology of opens. The
proof uses smaller simultaneous line charts, not global-section freeness. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleTensorLocallyBijective

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicLineModuleTensorPairing
open HolomorphicLineModuleTensorLocal HolomorphicLineModuleTensorPresheaf
open HolomorphicLineTensor
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

instance tensorPresheafHom_locallySurjective :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of B))
      (tensorPresheafHom IB Z W) where
  imageSieve_mem {U} s x hx := by
    let V : Opens B := U ⊓ ⟨Z.baseSet (Z.indexAt x) ∩ W.baseSet (W.indexAt x),
      (Z.isOpen_baseSet _).inter (W.isOpen_baseSet _)⟩
    let j : V ⟶ U := homOfLE inf_le_left
    refine ⟨V, j, ?_, ⟨hx, Z.mem_baseSet_at x, W.mem_baseSet_at x⟩⟩
    exact (tensorMap_bijective_of_le IB Z W (Z.indexAt x) (W.indexAt x) V
      (fun _ h => h.2.1) (fun _ h => h.2.2)).surjective
        ((moduleSheaf IB (tensorCore Z W)).val.map j.op s)

instance tensorPresheafHom_locallyInjective :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology (TopCat.of B))
      (tensorPresheafHom IB Z W) where
  equalizerSieve_mem {U} s t h x hx := by
    let V : Opens B := U.unop ⊓ ⟨Z.baseSet (Z.indexAt x) ∩ W.baseSet (W.indexAt x),
      (Z.isOpen_baseSet _).inter (W.isOpen_baseSet _)⟩
    let j : V ⟶ U.unop := homOfLE inf_le_left
    refine ⟨V, j, ?_, ⟨hx, Z.mem_baseSet_at x, W.mem_baseSet_at x⟩⟩
    apply (tensorMap_bijective_of_le IB Z W (Z.indexAt x) (W.indexAt x) V
      (fun _ h => h.2.1) (fun _ h => h.2.2)).injective
    change (tensorPresheafHom IB Z W).app (op V) ((tensorPresheaf IB Z W).map j.op s) =
      (tensorPresheafHom IB Z W).app (op V) ((tensorPresheaf IB Z W).map j.op t)
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg ((moduleSheaf IB (tensorCore Z W)).val.map j.op) h

end
end QuaternionicSymmetry.HolomorphicLineModuleTensorLocallyBijective
