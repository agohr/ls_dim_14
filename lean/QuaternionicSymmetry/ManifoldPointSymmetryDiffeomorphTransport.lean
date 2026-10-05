import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! A differential `-Id` at a fixed point is invariant under a genuine
diffeomorphism of smooth manifolds. This source-free bridge is useful when
refining or changing model coordinates for a Riemannian point symmetry. -/

namespace QuaternionicSymmetry.ManifoldPointSymmetryDiffeomorphTransport

open Manifold
open scoped Manifold ContDiff
noncomputable section

variable {E V H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

theorem conjugate_mfderiv_neg
    (D : Diffeomorph I J M N ∞) (S : Diffeomorph I I M M ∞)
    (x : M) (hfix : S x = x)
    (hneg : ∀ v : TangentSpace I x,
      mfderiv I I (S : M → M) x v = -v)
    (v : TangentSpace J (D x)) :
    mfderiv J J (D.symm.trans S |>.trans D : N → N) (D x) v = -v := by
  have hcancel :
      mfderiv I J (D : M → N) x
        (mfderiv J I (D.symm : N → M) (D x) v) = v := by
    have hx : (D.symm : N → M) (D x) = x := D.symm_apply_apply x
    have hcomp := mfderiv_comp (D x)
      (D.contMDiff.mdifferentiable (by simp) (D.symm (D x)))
      (D.symm.contMDiff.mdifferentiable (by simp) (D x))
    have hid : ((D : M → N) ∘ (D.symm : N → M)) = id := by
      funext y
      exact D.apply_symm_apply y
    rw [hid, mfderiv_id] at hcomp
    rw [hx] at hcomp
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using congrArg (fun L => L v) hcomp.symm
  have hchain :
      mfderiv J J (D.symm.trans S |>.trans D : N → N) (D x) v =
        mfderiv I J (D : M → N) x
          (mfderiv I I (S : M → M) x
            (mfderiv J I (D.symm : N → M) (D x) v)) := by
    have h₁ := mfderiv_comp (D x)
      (S.contMDiff.mdifferentiable (by simp) (D.symm (D x)))
      (D.symm.contMDiff.mdifferentiable (by simp) (D x))
    have h₂ := mfderiv_comp (D x)
      (D.contMDiff.mdifferentiable (by simp) ((S : M → M) (D.symm (D x))))
      ((S.contMDiff.comp D.symm.contMDiff).mdifferentiable (by simp) (D x))
    have hx : (D.symm : N → M) (D x) = x := D.symm_apply_apply x
    rw [hx] at h₁
    simp only [Function.comp_apply] at h₂
    rw [hx, hfix] at h₂
    change (mfderiv J J
      ((D : M → N) ∘ (S : M → M) ∘ (D.symm : N → M)) (D x)) v = _
    rw [h₂, h₁]
    rfl
  rw [hchain, hneg, map_neg, hcancel]

end
end QuaternionicSymmetry.ManifoldPointSymmetryDiffeomorphTransport
