import QuaternionicSymmetry.ManifoldQuaternionicInducedTotalGeodesy
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! The local differential consequence of a smooth rectangular
quaternionic intertwining equation. This algebra is independent of the
geometric source theorem and is later applied to the actual adapted maps. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionAlgebra
open ManifoldTwistorSphereBundle
open Filter
open scoped Topology
noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev R3 := Fin 3 → ℝ

theorem fderiv_of_rectangular_intertwining
    (SR : R3 →L[ℝ] (F →L[ℝ] F))
    (SP : R3 →L[ℝ] (E →L[ℝ] E))
    (A : F → F →L[ℝ] E)
    (C : F → R3 →L[ℝ] R3)
    (y : F) (hA : DifferentiableAt ℝ A y)
    (hC : DifferentiableAt ℝ C y)
    (hInter : ∀ᶠ z in 𝓝 y, ∀ (a : R3) (v : F),
      A z (SR a v) = SP (C z a) (A z v))
    (u : F) (a : R3) (v : F) :
    (fderiv ℝ A y u) (SR a v) =
      SP ((fderiv ℝ C y u) a) (A y v) +
        SP (C y a) ((fderiv ℝ A y u) v) := by
  have hAv : HasFDerivAt (fun z => A z v)
      ((fderiv ℝ A y).flip v) y := by
    simpa using hA.hasFDerivAt.clm_apply (hasFDerivAt_const v y)
  have hCa : HasFDerivAt (fun z => C z a)
      ((fderiv ℝ C y).flip a) y := by
    simpa using hC.hasFDerivAt.clm_apply (hasFDerivAt_const a y)
  have hSP : HasFDerivAt (fun z => SP (C z a))
      (SP.comp ((fderiv ℝ C y).flip a)) y :=
    SP.hasFDerivAt.comp y hCa
  have hRhs := hSP.clm_apply hAv
  have hLhs := hA.hasFDerivAt.clm_apply (hasFDerivAt_const (SR a v) y)
  have hfun : (fun z => A z (SR a v)) =ᶠ[𝓝 y]
      (fun z => SP (C z a) (A z v)) := by
    filter_upwards [hInter] with z hz
    exact hz a v
  have hd := congrArg (fun L : F →L[ℝ] E => L u) hfun.fderiv_eq
  rw [hLhs.fderiv, hRhs.fderiv] at hd
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hd
  simpa [add_comm] using hd

/-- Vanishing covariant Hessian and the differentiated intertwining law
force the rank-three connection defect to annihilate the actual image of
the rectangular inclusion. This is pure internal algebra; faithful
quaternionic action on one nonzero image vector is a separate cancellation
step. -/
theorem connection_defect_annihilates_image
    (SR : R3 →L[ℝ] (F →L[ℝ] F))
    (SP : R3 →L[ℝ] (E →L[ℝ] E))
    (A : F → F →L[ℝ] E)
    (C : F → R3 →L[ℝ] R3)
    (y : F) (hA : DifferentiableAt ℝ A y)
    (hC : DifferentiableAt ℝ C y)
    (hInter : ∀ᶠ z in 𝓝 y, ∀ (a : R3) (v : F),
      A z (SR a v) = SP (C z a) (A z v))
    (u : F)
    (ΓR : F →L[ℝ] F) (ΓP : E →L[ℝ] E)
    (ΩR ΩP : R3 →L[ℝ] R3)
    (hTot : ∀ v : F, (fderiv ℝ A y u) v =
      -ΓP (A y v) + A y (ΓR v))
    (hCommR : ∀ (a : R3) (v : F),
      ΓR (SR a v) - SR a (ΓR v) = SR (ΩR a) v)
    (hCommP : ∀ (b : R3) (w : E),
      ΓP (SP b w) - SP b (ΓP w) = SP (ΩP b) w)
    (a : R3) (v : F) :
    SP ((fderiv ℝ C y u) a + ΩP (C y a) - C y (ΩR a)) (A y v) = 0 := by
  have hAt (b : R3) (w : F) :
      A y (SR b w) = SP (C y b) (A y w) :=
    (Filter.Eventually.self_of_nhds hInter) b w
  have hGR : ΓR (SR a v) = SR (ΩR a) v + SR a (ΓR v) :=
    sub_eq_iff_eq_add.mp (hCommR a v)
  have hGP : ΓP (SP (C y a) (A y v)) =
      SP (ΩP (C y a)) (A y v) + SP (C y a) (ΓP (A y v)) :=
    sub_eq_iff_eq_add.mp (hCommP (C y a) (A y v))
  have hd := fderiv_of_rectangular_intertwining SR SP A C y hA hC hInter u a v
  rw [hTot (SR a v), hTot v, hAt a v, hGR,
    map_add, hAt (ΩR a) v, hAt a (ΓR v), hGP] at hd
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply] at hd ⊢
  simp only [map_neg] at hd
  let U := SP (ΩP (C y a)) (A y v)
  let V := SP (C y a) (ΓP (A y v))
  let W := SP (C y (ΩR a)) (A y v)
  let X := SP (C y a) (A y (ΓR v))
  let D := SP ((fderiv ℝ C y u) a) (A y v)
  change -(U + V) + (W + X) = D + (-V + X) at hd
  change D + U - W = 0
  calc
    D + U - W = (D + (-V + X)) - (-(U + V) + (W + X)) := by abel
    _ = 0 := by rw [← hd]; abel

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionAlgebra
