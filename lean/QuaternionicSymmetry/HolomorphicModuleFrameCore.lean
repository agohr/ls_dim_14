import QuaternionicSymmetry.HolomorphicModuleFrameTransition

/-! An actual holomorphic line-bundle core reconstructed from local frames
of an arbitrary locally free rank-one module sheaf. Its transition functions
are computed from that sheaf, and their cocycle is proved internally. The
comparison of its section sheaf with the original sheaf is a further step. -/

namespace QuaternionicSymmetry.HolomorphicModuleFrameCore

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicModuleLocalFrame
open HolomorphicModuleFrameTransition
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (M : SheafOfModules.{0} (structureSheaf (B := B) IB))

/-- An actual open cover with local sheaf frames. The only supplied data
are local freeness data; no bundle or comparison theorem is a field. -/
structure FrameCover (ι : Type*) where
  openSet : ι → Opens B
  indexAt : B → ι
  mem_openSet_at (x : B) : x ∈ openSet (indexAt x)
  frame (i : ι) : LocalFrame IB M (openSet i)

def framesOfLocallyFree (hM : IsLocallyFreeRankOne IB M) : FrameCover IB M B where
  openSet x := (hM x).choose
  indexAt x := x
  mem_openSet_at x := (hM x).choose_spec.1
  frame x := (hM x).choose_spec.2.some

variable {IB M} {ι : Type*} (A : FrameCover IB M ι)

/-- Scalar multiplication by the actual sheaf-frame transition gives the
coordinate changes of a genuine complex line-bundle core. -/
def lineCore : VectorBundleCore ℂ B ℂ ι where
  baseSet i := A.openSet i
  isOpen_baseSet i := (A.openSet i).isOpen
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_openSet_at
  coordChange i j x := scalar (A.frame i) (A.frame j) x • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by
    rw [scalar_self (A.frame i) x hx]
    simp
  continuousOn_coordChange i j :=
    (scalar_holomorphic (A.frame i) (A.frame j)).continuousOn.smul continuousOn_const
  coordChange_comp i j k x hx v := by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← mul_assoc, scalar_comp (A.frame i) (A.frame j) (A.frame k) x hx]

instance lineCore_isContMDiff : (lineCore A).IsContMDiff IB ∞ where
  contMDiffOn_coordChange i j :=
    (scalar_holomorphic (A.frame i) (A.frame j)).smul contMDiffOn_const

theorem lineCore_transitionScalar (i j : ι) (x : B) :
    HolomorphicLinePowers.transitionScalar (lineCore A) i j x =
      scalar (A.frame i) (A.frame j) x := by
  simp [HolomorphicLinePowers.transitionScalar, lineCore]

variable (IB M)

/-- A line core extracted from arbitrary local rank-one sheaf freeness,
not from an assumed line-bundle representation. -/
def coreOfLocallyFree (hM : IsLocallyFreeRankOne IB M) : VectorBundleCore ℂ B ℂ B :=
  lineCore (framesOfLocallyFree IB M hM)

instance coreOfLocallyFree_isContMDiff (hM : IsLocallyFreeRankOne IB M) :
    (coreOfLocallyFree IB M hM).IsContMDiff IB ∞ :=
  lineCore_isContMDiff _

end
end QuaternionicSymmetry.HolomorphicModuleFrameCore
