import QuaternionicSymmetry.HolomorphicLineCorePullbackSections
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! A holomorphic line on an actual one-point base has a nonzero global
section and a one-dimensional section space. No extension from an ambient
manifold and no classification input is used. -/

namespace QuaternionicSymmetry.HolomorphicLinePointSections

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  [Subsingleton B] (IB : ModelWithCorners ℂ F H)
  (L : LineCore (B := B) IB)

def constantSection (c : ℂ) : GlobalSections IB L := by
  letI := L.holomorphic
  refine ⟨fun _ => c, ?_⟩
  intro x
  have hfun : (fun y : B => Bundle.TotalSpace.mk' ℂ y
      (show L.core.Fiber y from c)) =
      (fun _ : B => Bundle.TotalSpace.mk' ℂ x
        (show L.core.Fiber x from c)) := by
    funext y
    cases Subsingleton.elim y x
    rfl
  rw [hfun]
  exact contMDiffAt_const

def evaluationEquiv (x : B) : GlobalSections IB L ≃ₗ[ℂ] ℂ where
  toFun s := s x
  invFun c := constantSection IB L c
  left_inv s := by
    apply ContMDiffSection.ext
    intro y
    change s x = s y
    exact congrArg s (Subsingleton.elim x y)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_sections_eq_one (x : B) :
    Module.finrank ℂ (GlobalSections IB L) = 1 := by
  rw [(evaluationEquiv IB L x).finrank_eq]
  exact CommSemiring.finrank_self ℂ

theorem globallyGenerated : GloballyGenerated IB L := by
  intro x
  refine ⟨constantSection IB L 1, ?_⟩
  change (1 : ℂ) ≠ 0
  exact one_ne_zero

end
end QuaternionicSymmetry.HolomorphicLinePointSections
