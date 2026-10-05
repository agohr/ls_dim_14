import QuaternionicSymmetry.HolomorphicModuleFrameCore

/-! The original module sheaf and the reconstructed line's section sheaf
are genuinely linearly isomorphic over each frame neighborhood. The local
isomorphisms commute with restrictions and agree on all chart overlaps. -/

namespace QuaternionicSymmetry.HolomorphicModuleFrameLocalComparison

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicLineModuleLocalFree
open HolomorphicModuleLocalFrame HolomorphicModuleFrameTransition
open HolomorphicModuleFrameCore
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  {IB : ModelWithCorners ℂ F H}
  {M : SheafOfModules.{0} (structureSheaf (B := B) IB)}
  (A : FrameCover IB M ι)

def localSectionEquiv (i : ι) (U : Opens B) (hU : U ≤ A.openSet i) :
    M.val.obj (op U) ≃ₗ[Functions IB U] sectionSubmodule IB (lineCore A) U :=
  ((A.frame i).coordinate U hU).trans
    (coordinateLinearEquiv IB (lineCore A) i U hU).symm

theorem localSectionEquiv_coordinate (i : ι) (U : Opens B)
    (hU : U ≤ A.openSet i) (s : M.val.obj (op U)) :
    coordinateLinearEquiv IB (lineCore A) i U hU (localSectionEquiv A i U hU s) =
      (A.frame i).coordinate U hU s :=
  (coordinateLinearEquiv IB (lineCore A) i U hU).apply_symm_apply _

theorem localSectionEquiv_restrict (i : ι) (U V : Opens B)
    (hVU : V ≤ U) (hU : U ≤ A.openSet i) (s : M.val.obj (op U)) :
    localSectionEquiv A i V (hVU.trans hU) (M.val.map (homOfLE hVU).op s) =
      (moduleSheaf IB (lineCore A)).val.map (homOfLE hVU).op
        (localSectionEquiv A i U hU s) := by
  apply (coordinateLinearEquiv IB (lineCore A) i V (hVU.trans hU)).injective
  rw [localSectionEquiv_coordinate, coordinate_restrict IB (lineCore A) i U V hVU hU,
    localSectionEquiv_coordinate]
  exact (A.frame i).restrict U V hVU hU s

/-- The local isomorphisms agree as actual maps into the same section
module, not merely after passing to isomorphism classes. -/
theorem localSectionEquiv_agree (i j : ι) (U : Opens B)
    (hi : U ≤ A.openSet i) (hj : U ≤ A.openSet j) (s : M.val.obj (op U)) :
    localSectionEquiv A i U hi s = localSectionEquiv A j U hj s := by
  apply (coordinateLinearEquiv IB (lineCore A) j U hj).injective
  apply Subtype.ext
  funext x
  change coordinateLinearEquiv IB (lineCore A) j U hj
      (localSectionEquiv A i U hi s) x =
    coordinateLinearEquiv IB (lineCore A) j U hj
      (localSectionEquiv A j U hj s) x
  rw [coordinate_transition IB (lineCore A) i j U hi hj,
    lineCore_transitionScalar, localSectionEquiv_coordinate,
    localSectionEquiv_coordinate, scalar_eq_localScalar (A.frame i) (A.frame j) U hi hj x]
  exact (congrArg (fun f : Functions IB U => f x)
    ((A.frame i).coordinate_change (A.frame j) U hi hj s)).symm

end
end QuaternionicSymmetry.HolomorphicModuleFrameLocalComparison
