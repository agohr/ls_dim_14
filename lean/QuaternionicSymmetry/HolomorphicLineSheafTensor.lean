import QuaternionicSymmetry.HolomorphicLineModuleTensorSheaf
import QuaternionicSymmetry.HolomorphicLineSheafClasses
import QuaternionicSymmetry.HolomorphicModuleLocalFrameIso

/-! Tensoring arbitrary locally free rank-one holomorphic module sheaves
using the actual sheafification of their tensor presheaf. Reconstruction
proves local freeness of this object and identifies it with tensoring the
actual line bundles. -/

namespace QuaternionicSymmetry.HolomorphicLineSheafTensor

open CategoryTheory TopologicalSpace Manifold
open HolomorphicLineModuleSheaf HolomorphicLineModuleTensorPresheaf
open HolomorphicLineModuleTensorSheaf HolomorphicLineTensor
open HolomorphicLineSheafClasses HolomorphicLineCoreClasses
open HolomorphicModuleLocalFrame HolomorphicModuleLocalFrameIso
open HolomorphicModuleFrameReconstruction
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

def tensorModuleSheaf
    (M N : SheafOfModules.{0} (structureSheaf (B := B) IB)) :
    SheafOfModules.{0} (structureSheaf (B := B) IB) :=
  (PresheafOfModules.sheafification (𝟙 (structureSheaf (B := B) IB).val)).obj
    (PresheafOfModules.Monoidal.tensorObj
      (R := (structureCommSheaf (B := B) IB).val) M.val N.val)

def tensorModuleSheafIso
    {M M' N N' : SheafOfModules.{0} (structureSheaf (B := B) IB)}
    (e : M ≅ M') (f : N ≅ N') :
    tensorModuleSheaf IB M N ≅ tensorModuleSheaf IB M' N' := by
  letI : MonoidalCategory (PresheafOfModules.{0} (structureSheaf (B := B) IB).val) :=
    PresheafOfModules.monoidalCategory (R := (structureCommSheaf (B := B) IB).val)
  exact (PresheafOfModules.sheafification (𝟙 (structureSheaf (B := B) IB).val)).mapIso
    (MonoidalCategory.tensorIso
      ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso f))

def tensorRepresentationIso (S T : LineSheaf (B := B) IB) :
    tensorModuleSheaf IB S.sheaf T.sheaf ≅
      moduleSheaf IB (tensorCore (toLineCore IB S).core (toLineCore IB T).core) := by
  letI := (toLineCore IB S).holomorphic
  letI := (toLineCore IB T).holomorphic
  exact tensorModuleSheafIso IB
    (reconstructionIso IB S.sheaf S.locallyFree)
    (reconstructionIso IB T.sheaf T.locallyFree) ≪≫
      tensorSheafIso IB (toLineCore IB S).core (toLineCore IB T).core

/-- This is the genuine sheaf tensor, not a product defined by moving
arbitrary classes across a bijection. -/
def tensorLineSheaf (S T : LineSheaf (B := B) IB) : LineSheaf (B := B) IB where
  sheaf := tensorModuleSheaf IB S.sheaf T.sheaf
  locallyFree := by
    letI := (toLineCore IB S).holomorphic
    letI := (toLineCore IB T).holomorphic
    exact locallyFree_of_iso IB (tensorRepresentationIso IB S T)
      (moduleSheaf_locallyFreeRankOne IB _)

theorem tensorLineSheaf_respects {S S' T T' : LineSheaf (B := B) IB}
    (hS : SheafIsomorphic IB S S') (hT : SheafIsomorphic IB T T') :
    SheafIsomorphic IB (tensorLineSheaf IB S T) (tensorLineSheaf IB S' T') := by
  obtain ⟨e⟩ := hS
  obtain ⟨f⟩ := hT
  exact ⟨tensorModuleSheafIso IB e f⟩

theorem toLineSheaf_tensor (L K : LineCore.{0} (B := B) IB) :
    SheafIsomorphic IB (tensorLineSheaf IB (toLineSheaf IB L) (toLineSheaf IB K))
      (toLineSheaf IB (L.tensor IB K)) := by
  letI := L.holomorphic
  letI := K.holomorphic
  exact ⟨tensorSheafIso IB L.core K.core⟩

end
end QuaternionicSymmetry.HolomorphicLineSheafTensor
