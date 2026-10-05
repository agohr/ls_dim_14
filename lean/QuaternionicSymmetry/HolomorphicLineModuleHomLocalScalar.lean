import QuaternionicSymmetry.HolomorphicLineModuleGaugeIso

/-! A genuine homomorphism of holomorphic line-section module sheaves is
multiplication by a holomorphic scalar in any pair of local line charts.
The scalar is computed from the image of the actual local unit frame and
is natural under restriction. This is the reverse comparison's local step. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleHomLocalScalar

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicLineModuleLocalFree
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

def sectionMap (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W) (U : Opens B) :
    sectionSubmodule IB Z U →ₗ[Functions IB U] sectionSubmodule IB W U :=
  (φ.val.app (op U)).hom

def localScalar (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (i : ι) (a : κ) (U : Opens B)
    (hZ : (U : Set B) ⊆ Z.baseSet i) (hW : (U : Set B) ⊆ W.baseSet a) :
    Functions IB U :=
  coordinateLinearEquiv IB W a U hW
    (sectionMap IB Z W φ U ((coordinateLinearEquiv IB Z i U hZ).symm 1))

theorem sectionMap_coordinates
    (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (i : ι) (a : κ) (U : Opens B)
    (hZ : (U : Set B) ⊆ Z.baseSet i) (hW : (U : Set B) ⊆ W.baseSet a)
    (s : sectionSubmodule IB Z U) :
    coordinateLinearEquiv IB W a U hW (sectionMap IB Z W φ U s) =
      localScalar IB Z W φ i a U hZ hW * coordinateLinearEquiv IB Z i U hZ s := by
  let cZ := coordinateLinearEquiv IB Z i U hZ
  let cW := coordinateLinearEquiv IB W a U hW
  have hs : s = (cZ s) • cZ.symm 1 := by
    apply cZ.injective
    simp
  calc
    cW (sectionMap IB Z W φ U s) =
        cW (sectionMap IB Z W φ U ((cZ s) • cZ.symm 1)) :=
      congrArg (fun t => cW (sectionMap IB Z W φ U t)) hs
    _ = (cZ s) • cW (sectionMap IB Z W φ U (cZ.symm 1)) := by
      rw [map_smul, map_smul]
    _ = localScalar IB Z W φ i a U hZ hW * cZ s := by
      exact mul_comm _ _

omit [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] in
theorem sectionMap_restrict
    (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (U V : Opens B) (hVU : V ≤ U) (s : sectionSubmodule IB Z U) :
    sectionMap IB Z W φ V ((moduleSheaf IB Z).val.map (homOfLE hVU).op s) =
      (moduleSheaf IB W).val.map (homOfLE hVU).op (sectionMap IB Z W φ U s) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE hVU).op s

/-- The literal unit-coordinate section restricts to the same unit frame
on every smaller open in its chart. -/
theorem unitFrame_restrict
    (i : ι) (U V : Opens B) (hVU : V ≤ U) (hZ : (U : Set B) ⊆ Z.baseSet i) :
    (moduleSheaf IB Z).val.map (homOfLE hVU).op
      ((coordinateLinearEquiv IB Z i U hZ).symm 1) =
      (coordinateLinearEquiv IB Z i V (fun _ hx => hZ (hVU hx))).symm 1 := by
  rfl

theorem localScalar_restrict
    (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (i : ι) (a : κ) (U V : Opens B) (hVU : V ≤ U)
    (hZ : (U : Set B) ⊆ Z.baseSet i) (hW : (U : Set B) ⊆ W.baseSet a) :
    localScalar IB Z W φ i a V (fun _ hx => hZ (hVU hx)) (fun _ hx => hW (hVU hx)) =
      ContMDiffMap.restrictRingHom IB 𝓘(ℂ,ℂ) ℂ hVU
        (localScalar IB Z W φ i a U hZ hW) := by
  unfold localScalar
  rw [← unitFrame_restrict IB Z i U V hVU hZ]
  rw [sectionMap_restrict]
  exact coordinate_restrict IB W a U V hVU hW _

end
end QuaternionicSymmetry.HolomorphicLineModuleHomLocalScalar
