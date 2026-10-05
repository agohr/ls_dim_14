import QuaternionicSymmetry.HolomorphicModuleLocalMapMorphism

/-! Reconstruction of an arbitrary locally free rank-one analytic module
sheaf as the actual section sheaf of a holomorphic complex line core. Both
maps are glued from the original local frames; their inverse laws are
checked by the sheaf's own local uniqueness. No classification input is used. -/

namespace QuaternionicSymmetry.HolomorphicModuleFrameReconstruction

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicModuleLocalFrame
open HolomorphicModuleFrameCore HolomorphicModuleFrameLocalComparison
open HolomorphicModuleLocalMapGluing HolomorphicModuleLocalMapMorphism
open scoped Manifold ContDiff
noncomputable section

variable {B ι : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  {IB : ModelWithCorners ℂ F H}
  {M : SheafOfModules.{0} (structureSheaf (B := B) IB)}
  (A : FrameCover IB M ι)

def forwardLocalMaps : LocalMaps M (moduleSheaf IB (lineCore A)) A.openSet where
  cover x := ⟨A.indexAt x, A.mem_openSet_at x⟩
  app i U hU := (localSectionEquiv A i U hU).toLinearMap
  restrict := localSectionEquiv_restrict A
  agree := localSectionEquiv_agree A

def inverseLocalMaps : LocalMaps (moduleSheaf IB (lineCore A)) M A.openSet where
  cover x := ⟨A.indexAt x, A.mem_openSet_at x⟩
  app i U hU := (localSectionEquiv A i U hU).symm.toLinearMap
  restrict i U V hVU hU s := by
    apply (localSectionEquiv A i V (hVU.trans hU)).injective
    change localSectionEquiv A i V (hVU.trans hU)
        ((localSectionEquiv A i V (hVU.trans hU)).symm
          ((moduleSheaf IB (lineCore A)).val.map (homOfLE hVU).op s)) =
      localSectionEquiv A i V (hVU.trans hU)
        (M.val.map (homOfLE hVU).op ((localSectionEquiv A i U hU).symm s))
    rw [LinearEquiv.apply_symm_apply, localSectionEquiv_restrict A i U V hVU hU,
      LinearEquiv.apply_symm_apply]
  agree i j U hi hj s := by
    apply (localSectionEquiv A i U hi).injective
    change localSectionEquiv A i U hi ((localSectionEquiv A i U hi).symm s) =
      localSectionEquiv A i U hi ((localSectionEquiv A j U hj).symm s)
    rw [LinearEquiv.apply_symm_apply, localSectionEquiv_agree A i j U hi hj,
      LinearEquiv.apply_symm_apply]

/-- The original arbitrary locally framed sheaf is isomorphic to the
actual holomorphic section sheaf of the core reconstructed from its frames. -/
def frameReconstructionIso : M ≅ moduleSheaf IB (lineCore A) where
  hom := glueHom (forwardLocalMaps A)
  inv := glueHom (inverseLocalMaps A)
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change image (inverseLocalMaps A) U.unop
      (image (forwardLocalMaps A) U.unop s) = s
    apply eq_of_piece_restrict (inverseLocalMaps A) U.unop
    intro i
    rw [image_restrict_piece]
    change (localSectionEquiv A i (pieces (O := A.openSet) U.unop i) inf_le_right).symm
        ((moduleSheaf IB (lineCore A)).val.map (homOfLE inf_le_left).op
          (image (forwardLocalMaps A) U.unop s)) = _
    rw [image_restrict_piece]
    exact (localSectionEquiv A i (pieces (O := A.openSet) U.unop i)
      inf_le_right).symm_apply_apply _
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change image (forwardLocalMaps A) U.unop
      (image (inverseLocalMaps A) U.unop s) = s
    apply eq_of_piece_restrict (forwardLocalMaps A) U.unop
    intro i
    rw [image_restrict_piece]
    change localSectionEquiv A i (pieces (O := A.openSet) U.unop i) inf_le_right
        (M.val.map (homOfLE inf_le_left).op (image (inverseLocalMaps A) U.unop s)) = _
    rw [image_restrict_piece]
    exact (localSectionEquiv A i (pieces (O := A.openSet) U.unop i)
      inf_le_right).apply_symm_apply _

variable (IB M)

/-- Essential surjectivity onto actual locally free rank-one module sheaves,
with a point-indexed core extracted from the local-freeness witnesses. -/
def reconstructionIso (hM : IsLocallyFreeRankOne IB M) :
    M ≅ moduleSheaf IB (coreOfLocallyFree IB M hM) :=
  frameReconstructionIso (framesOfLocallyFree IB M hM)

theorem exists_lineCore_representation (hM : IsLocallyFreeRankOne IB M) :
    ∃ L : HolomorphicLineCoreClasses.LineCore.{0} (B := B) IB,
      letI := L.holomorphic
      Nonempty (M ≅ moduleSheaf IB L.core) := by
  refine ⟨⟨B, coreOfLocallyFree IB M hM, inferInstance⟩, ?_⟩
  exact ⟨reconstructionIso IB M hM⟩

end
end QuaternionicSymmetry.HolomorphicModuleFrameReconstruction
