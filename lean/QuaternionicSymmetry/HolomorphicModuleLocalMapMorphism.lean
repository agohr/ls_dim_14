import QuaternionicSymmetry.HolomorphicModuleLocalMapGluing

/-! The actual maps on sections obtained by sheaf gluing commute with every
restriction and hence form a genuine module-sheaf morphism. -/

namespace QuaternionicSymmetry.HolomorphicModuleLocalMapMorphism

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicModuleLocalMapGluing
open scoped Manifold ContDiff
noncomputable section

variable {B ι : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  {IB : ModelWithCorners ℂ F H}
  {M N : SheafOfModules.{0} (structureSheaf (B := B) IB)}
  {O : ι → Opens B} (D : LocalMaps M N O)

/-- On every smaller open contained in one frame neighborhood, the glued
map is exactly the original local map. -/
theorem image_restrict_chart (i : ι) (U V : Opens B)
    (hVU : V ≤ U) (hVi : V ≤ O i) (s : M.val.obj (op U)) :
    N.val.map (homOfLE hVU).op (image D U s) =
      D.app i V hVi (M.val.map (homOfLE hVU).op s) := by
  have hVUi : V ≤ pieces (O := O) U i := le_inf hVU hVi
  calc
    _ = N.val.map (homOfLE hVUi).op
        (N.val.map (homOfLE (show pieces (O := O) U i ≤ U from inf_le_left)).op
          (image D U s)) := by
      rw [← N.val.map_comp_apply]
      rfl
    _ = N.val.map (homOfLE hVUi).op (localImages D U s i) := by
      rw [image_restrict_piece]
    _ = D.app i V hVi (M.val.map (homOfLE hVUi).op
        (M.val.map (homOfLE (show pieces (O := O) U i ≤ U from inf_le_left)).op s)) :=
      (D.restrict i (pieces (O := O) U i) V hVUi inf_le_right _).symm
    _ = _ := by rw [← M.val.map_comp_apply]; rfl

theorem image_restrict (U V : Opens B) (hVU : V ≤ U) (s : M.val.obj (op U)) :
    image D V (M.val.map (homOfLE hVU).op s) =
      N.val.map (homOfLE hVU).op (image D U s) := by
  apply eq_of_piece_restrict D V
  intro i
  rw [image_restrict_piece]
  have hPi : pieces (O := O) V i ≤ U := inf_le_left.trans hVU
  calc
    localImages D V (M.val.map (homOfLE hVU).op s) i =
        D.app i (pieces (O := O) V i) inf_le_right
          (M.val.map (homOfLE hPi).op s) := by
      unfold localImages
      rw [← M.val.map_comp_apply]
      rfl
    _ = N.val.map (homOfLE hPi).op (image D U s) :=
      (image_restrict_chart D i U (pieces (O := O) V i) hPi inf_le_right s).symm
    _ = _ := by rw [← N.val.map_comp_apply]; rfl

theorem image_eq_local (i : ι) (U : Opens B) (hU : U ≤ O i)
    (s : M.val.obj (op U)) : image D U s = D.app i U hU s := by
  simpa using image_restrict_chart D i U U le_rfl hU s

/-- The glued sections define an actual morphism in Mathlib's category of
module sheaves, not merely compatible functions on isomorphism classes. -/
def glueHom : M ⟶ N where
  val := {
    app := fun U => ModuleCat.ofHom
      (X := M.val.obj U) (Y := N.val.obj U) (imageLinearMap D U.unop)
    naturality := by
      intro U V j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact image_restrict D U.unop V.unop j.unop.le s }

end
end QuaternionicSymmetry.HolomorphicModuleLocalMapMorphism
