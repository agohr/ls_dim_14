import QuaternionicSymmetry.HolomorphicModuleLocalFrame

/-! Genuine module-sheaf isomorphisms transport rank-one local frames,
including their restriction naturality on every smaller open. -/

namespace QuaternionicSymmetry.HolomorphicModuleLocalFrameIso

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicModuleLocalFrame
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  {M N : SheafOfModules.{0} (structureSheaf (B := B) IB)}

def sectionIso (e : M ≅ N) (U : Opens B) :
    M.val.obj (op U) ≃ₗ[Functions IB U] N.val.obj (op U) :=
  ((SheafOfModules.evaluation (structureSheaf (B := B) IB) (op U)).mapIso e).toLinearEquiv

def frameOfIso (e : M ≅ N) {U : Opens B} (f : LocalFrame IB N U) :
    LocalFrame IB M U where
  coordinate V hV := (sectionIso IB e V).trans (f.coordinate V hV)
  restrict V W hWV hVU s := by
    change f.coordinate W (hWV.trans hVU)
      (e.hom.val.app (op W) (M.val.map (homOfLE hWV).op s)) = _
    rw [PresheafOfModules.naturality_apply]
    exact f.restrict V W hWV hVU (e.hom.val.app (op V) s)

theorem locallyFree_of_iso (e : M ≅ N) (hN : IsLocallyFreeRankOne IB N) :
    IsLocallyFreeRankOne IB M := by
  intro x
  obtain ⟨U, hxU, ⟨f⟩⟩ := hN x
  exact ⟨U, hxU, ⟨frameOfIso IB e f⟩⟩

end
end QuaternionicSymmetry.HolomorphicModuleLocalFrameIso
