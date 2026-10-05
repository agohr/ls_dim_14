import QuaternionicSymmetry.HolomorphicLineModuleTensorLocal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-! The actual tensor presheaf of holomorphic line-section modules and
its canonical map to sections of the tensor line. Naturality uses the
literal restrictions, including restriction of scalar functions. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleTensorPresheaf

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicLineModuleTensorPairing
open HolomorphicLineTensor
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)

/-- The same scalar functions, with their actual commutative ring structure. -/
abbrev structureCommSheaf : TopCat.Sheaf CommRingCat (TopCat.of B) :=
  smoothSheafCommRing IB 𝓘(ℂ,ℂ) B ℂ

theorem structureCommSheaf_forget :
    (structureCommSheaf (B := B) IB).val ⋙ forget₂ CommRingCat RingCat =
      (structureSheaf (B := B) IB).val := rfl

/-- Mathlib's genuine objectwise tensor of presheaves of modules. -/
def tensorPresheaf : PresheafOfModules (structureSheaf (B := B) IB).val :=
  PresheafOfModules.Monoidal.tensorObj
    (R := (structureCommSheaf (B := B) IB).val)
    (moduleSheaf IB Z).val (moduleSheaf IB W).val

/-- The canonical map, not an assumed global-section tensor isomorphism. -/
def tensorPresheafHom : tensorPresheaf IB Z W ⟶ (moduleSheaf IB (tensorCore Z W)).val where
  app U := ModuleCat.ofHom (X := (tensorPresheaf IB Z W).obj U)
    (Y := (moduleSheaf IB (tensorCore Z W)).val.obj U)
    (tensorMap IB Z W U.unop)
  naturality {U V} j := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    rfl

@[simp] theorem tensorPresheafHom_app (U : Opens B)
    (s : sectionSubmodule IB Z U ⊗[Functions IB U] sectionSubmodule IB W U) :
    (tensorPresheafHom IB Z W).app (op U) s = tensorMap IB Z W U s := rfl

end
end QuaternionicSymmetry.HolomorphicLineModuleTensorPresheaf
