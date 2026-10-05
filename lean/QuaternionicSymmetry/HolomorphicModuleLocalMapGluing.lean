import QuaternionicSymmetry.HolomorphicModuleFrameLocalComparison
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Actual gluing of compatible local linear morphisms of module sheaves
over the holomorphic function sheaf. The gluing uses the target's existing
sheaf axiom and retains the original restriction maps. -/

namespace QuaternionicSymmetry.HolomorphicModuleLocalMapGluing

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf
open scoped Manifold ContDiff
noncomputable section

variable {B ι : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  {IB : ModelWithCorners ℂ F H}
  (M N : SheafOfModules.{0} (structureSheaf (B := B) IB))

/-- Compatible local sheaf-linear maps on a genuine covering family. -/
structure LocalMaps (O : ι → Opens B) where
  cover : ∀ x : B, ∃ i, x ∈ O i
  app (i : ι) (U : Opens B) (hU : U ≤ O i) :
    M.val.obj (op U) →ₗ[Functions IB U] N.val.obj (op U)
  restrict (i : ι) (U V : Opens B) (hVU : V ≤ U) (hU : U ≤ O i)
      (s : M.val.obj (op U)) :
    app i V (hVU.trans hU) (M.val.map (homOfLE hVU).op s) =
      N.val.map (homOfLE hVU).op (app i U hU s)
  agree (i j : ι) (U : Opens B) (hi : U ≤ O i) (hj : U ≤ O j)
      (s : M.val.obj (op U)) : app i U hi s = app j U hj s

variable {M N} {O : ι → Opens B} (D : LocalMaps M N O)

abbrev pieces (U : Opens B) (i : ι) : Opens B := U ⊓ O i

include D in
theorem pieces_cover (U : Opens B) : U ≤ ⨆ i, pieces (O := O) U i := by
  intro x hx
  obtain ⟨i, hi⟩ := D.cover x
  exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩

def localImages (U : Opens B) (s : M.val.obj (op U)) (i : ι) :
    N.val.obj (op (pieces (O := O) U i)) :=
  D.app i (pieces (O := O) U i) inf_le_right
    (M.val.map (homOfLE (show pieces (O := O) U i ≤ U from inf_le_left)).op s)

theorem localImages_compatible (U : Opens B) (s : M.val.obj (op U)) :
    TopCat.Presheaf.IsCompatible N.val.presheaf (pieces (O := O) U)
      (localImages D U s) := by
  intro i j
  change N.val.map (Opens.infLELeft _ _).op (localImages D U s i) =
    N.val.map (Opens.infLERight _ _).op (localImages D U s j)
  let Ui := pieces (O := O) U i
  let Uj := pieces (O := O) U j
  let S := Ui ⊓ Uj
  have hi : S ≤ Ui := inf_le_left
  have hj : S ≤ Uj := inf_le_right
  have hiO : Ui ≤ O i := inf_le_right
  have hjO : Uj ≤ O j := inf_le_right
  have hiU : Ui ≤ U := inf_le_left
  have hjU : Uj ≤ U := inf_le_left
  calc
    _ = D.app i S (hi.trans hiO)
        (M.val.map (homOfLE hi).op (M.val.map (homOfLE hiU).op s)) :=
      (D.restrict i Ui S hi hiO _).symm
    _ = D.app j S (hj.trans hjO)
        (M.val.map (homOfLE hj).op (M.val.map (homOfLE hjU).op s)) := by
      rw [← M.val.map_comp_apply, ← M.val.map_comp_apply]
      exact D.agree i j S _ _ _
    _ = _ := D.restrict j Uj S hj hjO _

/-- A genuine global target section is obtained from the compatible local
images, uniquely characterized by its restrictions to this cover. -/
theorem existsUnique_image (U : Opens B) (s : M.val.obj (op U)) :
    ∃! t : N.val.obj (op U), ∀ i,
      N.val.map (homOfLE (show pieces (O := O) U i ≤ U from inf_le_left)).op t =
        localImages D U s i := by
  let NS : TopCat.Sheaf AddCommGrpCat (TopCat.of B) := ⟨N.val.presheaf, N.isSheaf⟩
  exact NS.existsUnique_gluing' (pieces (O := O) U) U
    (fun _ => homOfLE inf_le_left) (pieces_cover D U)
    (localImages D U s) (localImages_compatible D U s)

def image (U : Opens B) (s : M.val.obj (op U)) : N.val.obj (op U) :=
  (existsUnique_image D U s).choose

theorem image_restrict_piece (U : Opens B) (s : M.val.obj (op U)) (i : ι) :
    N.val.map (homOfLE (show pieces (O := O) U i ≤ U from inf_le_left)).op
      (image D U s) = localImages D U s i :=
  (existsUnique_image D U s).choose_spec.1 i

include D in
theorem eq_of_piece_restrict (U : Opens B) (s t : N.val.obj (op U))
    (h : ∀ i,
      N.val.map (homOfLE (show pieces (O := O) U i ≤ U from inf_le_left)).op s =
      N.val.map (homOfLE (show pieces (O := O) U i ≤ U from inf_le_left)).op t) :
    s = t := by
  let NS : TopCat.Sheaf AddCommGrpCat (TopCat.of B) := ⟨N.val.presheaf, N.isSheaf⟩
  exact NS.eq_of_locally_eq' (pieces (O := O) U) U
    (fun _ => homOfLE inf_le_left) (pieces_cover D U) s t h

theorem image_add (U : Opens B) (s t : M.val.obj (op U)) :
    image D U (s + t) = image D U s + image D U t := by
  apply eq_of_piece_restrict D U
  intro i
  rw [map_add, image_restrict_piece, image_restrict_piece, image_restrict_piece]
  simp only [localImages, map_add]

theorem image_smul (U : Opens B) (f : Functions IB U) (s : M.val.obj (op U)) :
    image D U (f • s) = f • image D U s := by
  apply eq_of_piece_restrict D U
  intro i
  rw [N.val.map_smul, image_restrict_piece, image_restrict_piece]
  simp only [localImages, M.val.map_smul, map_smul]

def imageLinearMap (U : Opens B) :
    M.val.obj (op U) →ₗ[Functions IB U] N.val.obj (op U) where
  toFun := image D U
  map_add' := image_add D U
  map_smul' := image_smul D U

end
end QuaternionicSymmetry.HolomorphicModuleLocalMapGluing
