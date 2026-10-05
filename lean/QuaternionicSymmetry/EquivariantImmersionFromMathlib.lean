import QuaternionicSymmetry.ManifoldFiniteFiberRank
import QuaternionicSymmetry.GeneralSmoothMapSource
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! The injective equivariant immersion theorem follows from the local rank
argument and the invertible differentials of the two smooth group actions. -/

namespace QuaternionicSymmetry.EquivariantImmersionFromMathlib

open GeneralSmoothMapSource ManifoldFiniteFiberRank
open scoped Manifold ContDiff Topology
open Function
noncomputable section

private def actionDiffeomorph
    {E F G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [TopologicalSpace M] [ChartedSpace F M]
    (a : SmoothLeftAction E F G M) (g : G) :
    Diffeomorph 𝓘(ℝ,F) 𝓘(ℝ,F) M M ∞ where
  toFun := a.act g
  invFun := a.act g⁻¹
  left_inv x := by rw [← a.mul_act, inv_mul_cancel, a.one_act]
  right_inv x := by rw [← a.mul_act, mul_inv_cancel, a.one_act]
  contMDiff_toFun := a.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := a.smooth.comp (contMDiff_const.prodMk contMDiff_id)

/-- Lee's injective equivariant rank conclusion, with no literature premise. -/
theorem equivariantImmersion : LeeEquivariantImmersionTheorem := by
  intro E F V G M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    a b f htrans hf hequiv hinj x
  have hIso : ∀ y, ∀ᶠ z in 𝓝 y, f z = f y → z = y :=
    fun _ => Filter.Eventually.of_forall (fun _ h => hinj h)
  obtain ⟨y, hy⟩ := exists_injective_mfderiv x hf hIso
  obtain ⟨g, hg⟩ := htrans y x
  let A := actionDiffeomorph a g
  let B := actionDiffeomorph b g
  have heq : f ∘ A = B ∘ f := funext (hequiv g)
  have hchain :
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f (A y)).comp
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) A y) =
      (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) B (f y)).comp
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f y) := by
    calc
      _ = mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) (f ∘ A) y :=
        (mfderiv_comp y (hf.mdifferentiableAt (by simp))
          (A.contMDiff.mdifferentiableAt (by simp))).symm
      _ = mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) (B ∘ f) y := by rw [heq]
      _ = _ := mfderiv_comp y (B.contMDiff.mdifferentiableAt (by simp))
        (hf.mdifferentiableAt (by simp))
  have hB : Injective (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) B (f y)) :=
    (B.mfderivToContinuousLinearEquiv (by simp) (f y)).injective
  have hA : Surjective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) A y) :=
    (A.mfderivToContinuousLinearEquiv (by simp) y).surjective
  have hc : Injective ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f (A y)).comp
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) A y)) := by
    rw [hchain]
    exact hB.comp hy
  change Injective ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f (A y)) ∘
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) A y)) at hc
  have hout : Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f (A y)) :=
    hc.of_comp_right hA
  change Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f (a.act g y)) at hout
  rwa [hg] at hout

end
end QuaternionicSymmetry.EquivariantImmersionFromMathlib
