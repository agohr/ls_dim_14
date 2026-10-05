import QuaternionicSymmetry.QuaternionicSecondFundamentalAlgebra
import QuaternionicSymmetry.ImmersionHessianCalculus
import QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionAlgebra
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal

/-! Differential quaternionic covariance and vanishing of the second
fundamental form, independently of any manifold or literature contract. -/
namespace QuaternionicSymmetry.QuaternionicImmersionHessian
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldQuaternionicRankThreeOrthogonal
open ManifoldQuaternionicInducedConnectionAlgebra
open ImmersionHessianCalculus
open QuaternionicSecondFundamentalAlgebra
open Filter
open scoped Topology
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Nontrivial E] [Nontrivial F]
private abbrev R3 := Fin 3 → ℝ

theorem coefficient_differentiableAt
    (SR : QuaternionicStructure F) (SP : QuaternionicStructure E)
    (A : F → F →L[ℝ] E) (C : F → R3 →L[ℝ] R3) (y : F)
    (hA : DifferentiableAt ℝ A y)
    (hiso : ∀ᶠ z in 𝓝 y, ∀ v w,
      inner ℝ (A z v) (A z w) = inner ℝ v w)
    (hInter : ∀ᶠ z in 𝓝 y, ∀ a v,
      A z (synth SR a v) = synth SP (C z a) (A z v)) :
    DifferentiableAt ℝ C y := by
  obtain ⟨w, hw⟩ := exists_norm_eq F (show (0 : ℝ) ≤ 1 by norm_num)
  have hAw : ∀ᶠ z in 𝓝 y, ‖A z w‖ = 1 := by
    filter_upwards [hiso] with z hz
    have h := hz w w
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hw] at h
    nlinarith [norm_nonneg (A z w)]
  have hentry (a : R3) (k : Fin 3) :
      DifferentiableAt ℝ (fun z => C z a k) y := by
    have hform : (fun z => C z a k) =ᶠ[𝓝 y]
        (fun z => inner ℝ (A z (synth SR a w))
          (synth SP (Pi.single k 1) (A z w))) := by
      filter_upwards [hInter, hAw] with z hz hn
      rw [hz, synth_eval_inner SP _ _ _ hn]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have ha := hA.clm_apply (differentiableAt_const (synth SR a w))
    have hb := (synth SP (Pi.single k 1)).differentiableAt.comp y
      (hA.clm_apply (differentiableAt_const w))
    exact (ha.inner ℝ hb).congr_of_eventuallyEq hform
  let e := ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := R3) (Fin 3)
  have hcols : DifferentiableAt ℝ
      (fun z => fun t : Fin 3 => C z (Pi.single t 1)) y := by
    apply differentiableAt_pi.mpr
    intro t
    apply differentiableAt_pi.mpr
    intro k
    exact hentry _ k
  have h := e.symm.differentiableAt.comp y hcols
  have heq : (fun z => e.symm (fun t : Fin 3 => C z (Pi.single t 1))) = C := by
    funext z
    apply e.injective
    rw [e.apply_symm_apply]
    ext t k
    simp [e, ContinuousLinearEquiv.piRing, LinearEquiv.piRing_apply,
      LinearEquiv.trans_apply]
  change DifferentiableAt ℝ (fun z => e.symm (fun t : Fin 3 => C z (Pi.single t 1))) y at h
  rwa [heq] at h

/-- The quaternionic commutator identities give Hessian covariance up to
an operator in the quaternionic span, applied to the tangent image. -/
theorem hessian_quaternionic_defect
    (SR : R3 →L[ℝ] (F →L[ℝ] F))
    (SP : R3 →L[ℝ] (E →L[ℝ] E))
    (A : F → F →L[ℝ] E) (C : F → R3 →L[ℝ] R3)
    (G : F → E) (y : F)
    (ΓP : E →L[ℝ] E →L[ℝ] E) (ΓR : F →L[ℝ] F →L[ℝ] F)
    (hA : DifferentiableAt ℝ A y) (hC : DifferentiableAt ℝ C y)
    (hInter : ∀ᶠ z in 𝓝 y, ∀ a v, A z (SR a v) = SP (C z a) (A z v))
    (ΩR ΩP : R3 →L[ℝ] R3) (u : F)
    (hCommR : ∀ a v, ΓR u (SR a v) - SR a (ΓR u v) = SR (ΩR a) v)
    (hCommP : ∀ b w, ΓP (fderiv ℝ G y u) (SP b w) -
      SP b (ΓP (fderiv ℝ G y u) w) = SP (ΩP b) w)
    (a : R3) (v : F) :
    hessian A G y ΓP ΓR u (SR a v) - SP (C y a) (hessian A G y ΓP ΓR u v) =
      SP ((fderiv ℝ C y u) a + ΩP (C y a) - C y (ΩR a)) (A y v) := by
  have hAt := hInter.self_of_nhds
  have hd := fderiv_of_rectangular_intertwining SR SP A C y hA hC hInter u a v
  have hGR : ΓR u (SR a v) = SR (ΩR a) v + SR a (ΓR u v) :=
    sub_eq_iff_eq_add.mp (hCommR a v)
  have hGP : ΓP (fderiv ℝ G y u) (SP (C y a) (A y v)) =
      SP (ΩP (C y a)) (A y v) + SP (C y a) (ΓP (fderiv ℝ G y u) (A y v)) :=
    sub_eq_iff_eq_add.mp (hCommP (C y a) (A y v))
  simp only [hessian, hd, hAt, hGR, hGP, map_add, map_sub,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  abel

end
end QuaternionicSymmetry.QuaternionicImmersionHessian
