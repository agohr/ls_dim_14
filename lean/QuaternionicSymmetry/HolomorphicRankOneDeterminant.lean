import QuaternionicSymmetry.HolomorphicDeterminantLine
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! A one-dimensional vector bundle with model `Fin 1 → ℂ` and its genuine
determinant line have the same transition coordinates under evaluation at
zero. In particular holomorphic local vector sections yield holomorphic
local determinant sections. -/

namespace QuaternionicSymmetry.HolomorphicRankOneDeterminant

open scoped Manifold ContDiff
open HolomorphicDeterminantLine
noncomputable section

theorem map_eq_scalar (T : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ)) :
    T = (T (fun _ => 1) 0) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
  ext v i
  have hv : v = v 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
    ext j
    simp [Subsingleton.elim j 0]
  have h : T v = v 0 • T (fun _ => 1) :=
    (congrArg T hv).trans (T.map_smul _ _)
  have hi := congrFun h i
  simpa [Subsingleton.elim i 0, mul_comm] using hi

theorem det_eq_scalar (T : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ)) :
    T.det = T (fun _ => 1) 0 := by
  have h := map_eq_scalar T
  rw [h]
  change LinearMap.det
    ((T (fun _ => 1) 0) • (LinearMap.id : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) = _
  rw [LinearMap.det_smul, LinearMap.det_id]
  simp

theorem det_mul_coordinate (T : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ))
    (v : Fin 1 → ℂ) : T.det * v 0 = T v 0 := by
  rw [det_eq_scalar]
  conv_rhs => rw [map_eq_scalar T]
  rfl

variable {B H G : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ G H) {ι : Type*}
  (Z : VectorBundleCore ℂ B (Fin 1 → ℂ) ι) [Z.IsContMDiff IB ∞]

theorem determinantSection_contMDiffOn (U : Set B)
    (s : ∀ x : B, Z.Fiber x)
    (hs : ContMDiffOn IB (IB.prod 𝓘(ℂ,Fin 1 → ℂ)) ∞
      (fun x => (⟨x,s x⟩ : Bundle.TotalSpace (Fin 1 → ℂ) Z.Fiber)) U) :
    ContMDiffOn IB (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun x => (⟨x,s x 0⟩ : Bundle.TotalSpace ℂ (determinantCore Z).Fiber)) U := by
  intro x hx
  apply Bundle.contMDiffWithinAt_totalSpace.mpr
  refine ⟨contMDiffWithinAt_id, ?_⟩
  have hv := (Bundle.contMDiffWithinAt_totalSpace.mp (hs x hx)).2
  have he := (ContinuousLinearMap.proj (0 : Fin 1) :
    (Fin 1 → ℂ) →L[ℂ] ℂ).contMDiff.contMDiffAt.comp_contMDiffWithinAt x hv
  change ContMDiffWithinAt IB 𝓘(ℂ,ℂ) ∞
    (fun y => transitionDet Z (Z.indexAt y) (Z.indexAt x) y * s y 0) U x
  convert he using 1
  funext y
  exact det_mul_coordinate _ _

end
end QuaternionicSymmetry.HolomorphicRankOneDeterminant
