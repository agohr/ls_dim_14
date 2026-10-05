import QuaternionicSymmetry.GeneralLeviCivitaIsometryNaturality
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Differentiating a genuine endomorphism-field intertwining law through
a smooth isometry chart map. This is the jet identity needed to turn
point-reflection invariance of the actual smooth Q-plane into ordinary
Levi-Civita parallelism. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaInvariantEndomorphismJet

open Filter
open scoped Manifold ContDiff Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem endomorphism_intertwining_first_jet
    (F : E → E) (A B : E → E →L[ℝ] E) (y u v : E)
    (hF : ContDiffAt ℝ 2 F y)
    (hA : DifferentiableAt ℝ A y)
    (hB : DifferentiableAt ℝ B (F y))
    (heq : ∀ᶠ z in 𝓝 y,
      B (F z) ((fderiv ℝ F z) v) = (fderiv ℝ F z) (A z v)) :
    let R := fderiv ℝ F
    let S := fderiv ℝ R y
    (fderiv ℝ B (F y)) (R y u) (R y v) + B (F y) (S u v) =
      S u (A y v) + R y (fderiv ℝ A y u v) := by
  dsimp only
  let R := fderiv ℝ F
  have hFd : DifferentiableAt ℝ F y := hF.differentiableAt (by norm_num)
  have hR : DifferentiableAt ℝ R y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hBF : DifferentiableAt ℝ (B ∘ F) y := hB.comp y hFd
  have hRv : DifferentiableAt ℝ (fun z => R z v) y :=
    hR.clm_apply (differentiableAt_const _)
  have hAv : DifferentiableAt ℝ (fun z => A z v) y :=
    hA.clm_apply (differentiableAt_const _)
  have hleft : DifferentiableAt ℝ (fun z => B (F z) (R z v)) y :=
    hBF.clm_apply hRv
  have hright : DifferentiableAt ℝ (fun z => R z (A z v)) y :=
    hR.clm_apply hAv
  have hd := congrArg (fun L : E →L[ℝ] E => L u)
    ((Filter.EventuallyEq.symm heq).fderiv_eq (𝕜 := ℝ))
  -- Reverse the eventual equality so the derivative is oriented left-to-right.
  have hd' : fderiv ℝ (fun z => B (F z) (R z v)) y u =
      fderiv ℝ (fun z => R z (A z v)) y u := hd.symm
  change fderiv ℝ (fun z => (B ∘ F) z ((fun z => R z v) z)) y u =
    fderiv ℝ (fun z => R z ((fun z => A z v) z)) y u at hd'
  rw [fderiv_clm_apply hBF hRv, fderiv_clm_apply hR hAv] at hd'
  have hcomp : fderiv ℝ (B ∘ F) y =
      (fderiv ℝ B (F y)).comp (R y) := fderiv_comp y hB hFd
  rw [hcomp] at hd'
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, Function.comp_apply] at hd'
  have hRv' : fderiv ℝ (fun z => R z v) y u = fderiv ℝ R y u v := by
    rw [fderiv_clm_apply hR (differentiableAt_const _)]
    simp
  have hAv' : fderiv ℝ (fun z => A z v) y u = fderiv ℝ A y u v := by
    rw [fderiv_clm_apply hA (differentiableAt_const _)]
    simp
  rw [hRv', hAv'] at hd'
  convert hd' using 1 <;> abel

end
end QuaternionicSymmetry.GeneralLeviCivitaInvariantEndomorphismJet
