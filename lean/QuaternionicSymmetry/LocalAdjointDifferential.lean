import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-! The local calculus underlying the derivative of the adjoint action.
Only the first two derivatives of multiplication in one chart are used. -/
namespace QuaternionicSymmetry.LocalAdjointDifferential

open scoped ContDiff Topology
open Filter Function
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Coordinate differential of left multiplication at the identity. -/
def leftMatrix (m : E × E → E) (a x : E) : E →L[ℝ] E :=
  (fderiv ℝ m (x,a)).comp (ContinuousLinearMap.inr ℝ E E)

/-- Coordinate differential of right multiplication at the identity. -/
def rightMatrix (m : E × E → E) (a x : E) : E →L[ℝ] E :=
  (fderiv ℝ m (a,x)).comp (ContinuousLinearMap.inl ℝ E E)

theorem leftMatrix_contDiffAt {m : E × E → E} {a : E}
    (hm : ContDiffAt ℝ 2 m (a,a)) : ContDiffAt ℝ 1 (leftMatrix m a) a := by
  have hd := (hm.fderiv_right (m := 1) (by norm_num)).comp (f := fun x : E => (x,a)) a
    (contDiffAt_id.prodMk contDiffAt_const)
  exact hd.clm_comp contDiffAt_const

theorem rightMatrix_contDiffAt {m : E × E → E} {a : E}
    (hm : ContDiffAt ℝ 2 m (a,a)) : ContDiffAt ℝ 1 (rightMatrix m a) a := by
  have hd := (hm.fderiv_right (m := 1) (by norm_num)).comp (f := fun x : E => (a,x)) a
    (contDiffAt_const.prodMk contDiffAt_id)
  exact hd.clm_comp contDiffAt_const

/-- Symmetry of the second derivative interchanges the left and right
coordinate multiplication matrices. -/
theorem mixed_partials {m : E × E → E} {a : E}
    (hm : ContDiffAt ℝ 2 m (a,a)) (u v : E) :
    (fderiv ℝ (rightMatrix m a) a u) v =
      (fderiv ℝ (leftMatrix m a) a v) u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ m) (a,a) :=
    (hm.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hl := (hd.hasFDerivAt.comp (f := fun x : E => (x,a)) a (hasFDerivAt_prodMk_left a a)).clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.inr ℝ E E) a)
  have hr := (hd.hasFDerivAt.comp (f := fun x : E => (a,x)) a (hasFDerivAt_prodMk_right a a)).clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.inl ℝ E E) a)
  rw [show fderiv ℝ (rightMatrix m a) a = _ from hr.fderiv,
    show fderiv ℝ (leftMatrix m a) a = _ from hl.fderiv]
  simpa using hm.isSymmSndFDerivAt (by norm_num) (0,u) (v,0)

lemma leftMatrix_eq_fderiv {m : E × E → E} {a x : E}
    (hm : DifferentiableAt ℝ m (x,a)) :
    leftMatrix m a x = fderiv ℝ (fun y => m (x,y)) a :=
  (hm.hasFDerivAt.comp (f := fun y => (x,y)) a
    (hasFDerivAt_prodMk_right x a)).fderiv.symm

lemma rightMatrix_eq_fderiv {m : E × E → E} {a x : E}
    (hm : DifferentiableAt ℝ m (a,x)) :
    rightMatrix m a x = fderiv ℝ (fun y => m (y,x)) a :=
  (hm.hasFDerivAt.comp (f := fun y => (y,x)) a
    (hasFDerivAt_prodMk_left a x)).fderiv.symm

/-- Differentiate the quotient of the right and left multiplication
matrices at the identity. This is the adjoint differential in a chart. -/
theorem quotient_differential {m : E × E → E} {a : E}
    (hm : ContDiffAt ℝ 2 m (a,a))
    (hA : leftMatrix m a a = ContinuousLinearMap.id ℝ E)
    (hB : rightMatrix m a a = ContinuousLinearMap.id ℝ E)
    (hInv : ∀ᶠ x in 𝓝 a, (rightMatrix m a x).IsInvertible)
    (v : E) :
    let C := fun x => (rightMatrix m a x).inverse (leftMatrix m a x v)
    DifferentiableAt ℝ C a ∧ ∀ u,
      fderiv ℝ C a u =
        (fderiv ℝ (leftMatrix m a) a u) v -
          (fderiv ℝ (leftMatrix m a) a v) u := by
  dsimp only
  let A := leftMatrix m a
  let B := rightMatrix m a
  let C := fun x => (B x).inverse (A x v)
  have hAc : ContDiffAt ℝ 1 A a := leftMatrix_contDiffAt hm
  have hBc : ContDiffAt ℝ 1 B a := rightMatrix_contDiffAt hm
  have hBi : ContDiffAt ℝ 1 (fun x => (B x).inverse) a := by
    have hi : ContDiffAt ℝ 1 (fun T : E →L[ℝ] E => T.inverse) (B a) := by
      rw [show B a = ContinuousLinearMap.id ℝ E from hB]
      exact contDiffAt_map_inverse (ContinuousLinearEquiv.refl ℝ E)
    exact hi.comp a hBc
  have hCc : ContDiffAt ℝ 1 C a := hBi.clm_apply (hAc.clm_apply contDiffAt_const)
  have hCd := hCc.differentiableAt (by norm_num)
  refine ⟨hCd, fun u => ?_⟩
  have hEq : (fun x => B x (C x)) =ᶠ[𝓝 a] (fun x => A x v) := by
    filter_upwards [hInv] with x hx
    exact hx.self_apply_inverse _
  have hCa : C a = v := by simp [C, A, B, hA, hB]
  have hd := congrArg (fun T : E →L[ℝ] E => T u) hEq.fderiv_eq
  rw [fderiv_clm_apply (hBc.differentiableAt (by norm_num)) hCd,
    fderiv_clm_apply (hAc.differentiableAt (by norm_num)) (differentiableAt_const v)] at hd
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    map_zero, zero_add, hCa] at hd
  rw [show B a = ContinuousLinearMap.id ℝ E from hB] at hd
  simp only [ContinuousLinearMap.id_apply] at hd
  change fderiv ℝ C a u = _
  rw [← mixed_partials hm u v]
  exact eq_sub_of_add_eq hd

end
end QuaternionicSymmetry.LocalAdjointDifferential
