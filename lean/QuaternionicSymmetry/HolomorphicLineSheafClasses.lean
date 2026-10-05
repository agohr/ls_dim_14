import QuaternionicSymmetry.HolomorphicModuleFrameReconstruction

/-! Isomorphism classes of actual locally free rank-one analytic module
sheaves are in bijection with cover-invariant holomorphic line-core classes.
This uses genuine sheaf reconstruction and the recovered all-overlap gauge,
not an assumed Picard classification. Tensor and cohomology comparisons are
not asserted by this set-level equivalence. -/

namespace QuaternionicSymmetry.HolomorphicLineSheafClasses

open CategoryTheory Manifold
open HolomorphicLineCoreClasses HolomorphicLineModuleSheaf
open HolomorphicLineModuleGaugeIso HolomorphicLineModuleIsoToGauge
open HolomorphicModuleLocalFrame HolomorphicModuleFrameCore
open HolomorphicModuleFrameReconstruction
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

/-- A genuine small locally free rank-one module sheaf over the actual
holomorphic function sheaf. -/
structure LineSheaf where
  sheaf : SheafOfModules.{0} (structureSheaf (B := B) IB)
  locallyFree : IsLocallyFreeRankOne IB sheaf

def SheafIsomorphic (S T : LineSheaf (B := B) IB) : Prop :=
  Nonempty (S.sheaf ≅ T.sheaf)

instance : Setoid (LineSheaf (B := B) IB) where
  r := SheafIsomorphic IB
  iseqv := {
    refl := fun S => ⟨Iso.refl S.sheaf⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩ }

abbrev SheafClass := Quotient (inferInstance : Setoid (LineSheaf (B := B) IB))

def toLineSheaf (L : LineCore.{0} (B := B) IB) : LineSheaf (B := B) IB := by
  letI := L.holomorphic
  exact ⟨moduleSheaf IB L.core, moduleSheaf_locallyFreeRankOne IB L.core⟩

def toLineCore (S : LineSheaf (B := B) IB) : LineCore.{0} (B := B) IB where
  Index := B
  core := coreOfLocallyFree IB S.sheaf S.locallyFree
  holomorphic := inferInstance

theorem toLineSheaf_respects {L K : LineCore.{0} (B := B) IB}
    (h : Isomorphic IB L K) : SheafIsomorphic IB (toLineSheaf IB L) (toLineSheaf IB K) := by
  letI := L.holomorphic
  letI := K.holomorphic
  obtain ⟨e⟩ := h
  exact ⟨gaugeSheafIso IB L.core K.core e⟩

theorem toLineCore_respects {S T : LineSheaf (B := B) IB}
    (h : SheafIsomorphic IB S T) : Isomorphic IB (toLineCore IB S) (toLineCore IB T) := by
  letI := (toLineCore IB S).holomorphic
  letI := (toLineCore IB T).holomorphic
  obtain ⟨e⟩ := h
  exact ⟨isoToGauge IB _ _
    ((reconstructionIso IB S.sheaf S.locallyFree).symm ≪≫ e ≪≫
      reconstructionIso IB T.sheaf T.locallyFree)⟩

theorem toLineCore_toLineSheaf (L : LineCore.{0} (B := B) IB) :
    Isomorphic IB (toLineCore IB (toLineSheaf IB L)) L := by
  letI := L.holomorphic
  letI := (toLineCore IB (toLineSheaf IB L)).holomorphic
  exact ⟨isoToGauge IB _ _ (reconstructionIso IB (moduleSheaf IB L.core)
    (moduleSheaf_locallyFreeRankOne IB L.core)).symm⟩

theorem toLineSheaf_toLineCore (S : LineSheaf (B := B) IB) :
    SheafIsomorphic IB (toLineSheaf IB (toLineCore IB S)) S :=
  ⟨(reconstructionIso IB S.sheaf S.locallyFree).symm⟩

/-- Cover-invariant bundle classes classify actual locally free rank-one
module sheaves up to their genuine categorical isomorphisms. -/
def classEquiv : CoreClass.{0} (B := B) IB ≃ SheafClass (B := B) IB where
  toFun := Quotient.map (toLineSheaf IB) (fun _ _ h => toLineSheaf_respects IB h)
  invFun := Quotient.map (toLineCore IB) (fun _ _ h => toLineCore_respects IB h)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h L => exact Quotient.sound (toLineCore_toLineSheaf IB L)
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h S => exact Quotient.sound (toLineSheaf_toLineCore IB S)

end
end QuaternionicSymmetry.HolomorphicLineSheafClasses
