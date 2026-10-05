import QuaternionicSymmetry.HolomorphicLineModuleTensorLocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact

/-! The section sheaf of the tensor line is canonically isomorphic to
the genuine sheafification of the tensor presheaf. Both universal
properties and the compatibility with the original bilinear pairing
are checked. No group structure is transported by an arbitrary bijection. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleTensorSheaf

open CategoryTheory TopologicalSpace Manifold
open HolomorphicLineModuleSheaf HolomorphicLineModuleTensorPresheaf
open HolomorphicLineModuleTensorLocallyBijective HolomorphicLineTensor
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

/-- The actual sheaf tensor product, obtained by the existing categorical
sheafification functor on the actual objectwise module tensor. -/
def tensorSheaf : SheafOfModules (structureSheaf (B := B) IB) :=
  (PresheafOfModules.sheafification (𝟙 (structureSheaf (B := B) IB).val)).obj
    (tensorPresheaf IB Z W)

def tensorSheafUnit : tensorPresheaf IB Z W ⟶ (tensorSheaf IB Z W).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheaf (B := B) IB).val)).unit.app (tensorPresheaf IB Z W)

/-- The section sheaf of the tensor line has the same sheafification
universal property, because the actual pairing is locally bijective. -/
def tensorSectionHomEquiv (N : SheafOfModules (structureSheaf (B := B) IB)) :
    (moduleSheaf IB (tensorCore Z W) ⟶ N) ≃ (tensorPresheaf IB Z W ⟶ N.val) :=
  (SheafOfModules.fullyFaithfulForget (structureSheaf (B := B) IB)).homEquiv.trans
    (PresheafOfModules.homEquivOfIsLocallyBijective
      (f := tensorPresheafHom IB Z W) N.isSheaf)

def tensorSheafComparison : tensorSheaf IB Z W ⟶ moduleSheaf IB (tensorCore Z W) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (structureSheaf (B := B) IB).val)).symm (tensorPresheafHom IB Z W)

omit [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] in
theorem tensorSheafUnit_comp_comparison :
    tensorSheafUnit IB Z W ≫ (tensorSheafComparison IB Z W).val =
      tensorPresheafHom IB Z W :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (structureSheaf (B := B) IB).val)).apply_symm_apply _

def tensorSheafComparisonInv : moduleSheaf IB (tensorCore Z W) ⟶ tensorSheaf IB Z W :=
  (tensorSectionHomEquiv IB Z W (tensorSheaf IB Z W)).symm (tensorSheafUnit IB Z W)

theorem tensorPresheafHom_comp_comparisonInv :
    tensorPresheafHom IB Z W ≫ (tensorSheafComparisonInv IB Z W).val =
      tensorSheafUnit IB Z W :=
  (tensorSectionHomEquiv IB Z W (tensorSheaf IB Z W)).apply_symm_apply _

/-- Canonical comparison with genuine sheafified tensor, characterized
by its compatibility with multiplication of actual local sections. -/
def tensorSheafIso : tensorSheaf IB Z W ≅ moduleSheaf IB (tensorCore Z W) where
  hom := tensorSheafComparison IB Z W
  inv := tensorSheafComparisonInv IB Z W
  hom_inv_id := by
    apply (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (structureSheaf (B := B) IB).val)).injective
    change tensorSheafUnit IB Z W ≫
      ((tensorSheafComparison IB Z W).val ≫ (tensorSheafComparisonInv IB Z W).val) =
      tensorSheafUnit IB Z W ≫ 𝟙 _
    rw [← Category.assoc, tensorSheafUnit_comp_comparison,
      tensorPresheafHom_comp_comparisonInv, Category.comp_id]
  inv_hom_id := by
    apply (tensorSectionHomEquiv IB Z W (moduleSheaf IB (tensorCore Z W))).injective
    change tensorPresheafHom IB Z W ≫
      ((tensorSheafComparisonInv IB Z W).val ≫ (tensorSheafComparison IB Z W).val) =
      tensorPresheafHom IB Z W ≫ 𝟙 _
    rw [← Category.assoc, tensorPresheafHom_comp_comparisonInv,
      tensorSheafUnit_comp_comparison, Category.comp_id]

end
end QuaternionicSymmetry.HolomorphicLineModuleTensorSheaf
