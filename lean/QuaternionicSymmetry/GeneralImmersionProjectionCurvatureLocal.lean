import QuaternionicSymmetry.GeneralImmersionProjectionCurvature
import QuaternionicSymmetry.GeneralImmersionGaussJetLocal
import QuaternionicSymmetry.GeneralImmersionProjectionDerivativeLocal

/-! Exact curvature of an immersed projection connection when Gauss and
tangent-fixed identities hold only on a neighborhood, as in true charts. -/

namespace QuaternionicSymmetry.GeneralImmersionProjectionCurvatureLocal

open GeneralImmersionGaussJetLocal
open GeneralImmersionProjectionDerivativeLocal
open GeneralImmersionThirdDerivativeSymmetry
open scoped ContDiff Topology
noncomputable section

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem projection_curvature_formula_local
    (f : E → V) (π : E → V →L[ℝ] V)
    (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (y u v w : E)
    (hf : ContDiffAt ℝ 3 f y)
    (hπ : DifferentiableAt ℝ π y)
    (hΓ : DifferentiableAt ℝ Γ y)
    (hGauss : ∀ᶠ z in 𝓝 y, ∀ a b,
      fderiv ℝ f z (Γ z a b) =
        π z (fderiv ℝ (fderiv ℝ f) z a b))
    (hfix : ∀ᶠ z in 𝓝 y, ∀ a,
      π z (fderiv ℝ f z a) = fderiv ℝ f z a) :
    (fderiv ℝ f y)
      ((fderiv ℝ Γ y u) v w + Γ y u (Γ y v w) -
        ((fderiv ℝ Γ y v) u w + Γ y v (Γ y u w))) =
      (fderiv ℝ π y u) ((fderiv ℝ π y v) (fderiv ℝ f y w)) -
        (fderiv ℝ π y v) ((fderiv ℝ π y u) (fderiv ℝ f y w)) := by
  have hf2 : ContDiffAt ℝ 2 f y := hf.of_le (by norm_num)
  have hdF : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdF2 : ContDiffAt ℝ 2 (fderiv ℝ f) y :=
    hf.fderiv_right (m := 2) (by norm_num)
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) y :=
    (hdF2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hGaussY := hGauss.self_of_nhds
  have hOne (a b c : E) :
      (fderiv ℝ f y)
        ((fderiv ℝ Γ y a) b c + Γ y a (Γ y b c)) =
      (fderiv ℝ π y a) ((fderiv ℝ π y b) (fderiv ℝ f y c)) +
        π y ((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y a) b c) := by
    have hj := derivative_projected_hessian_gauss_local
      f π Γ y a b c hdF hH hπ hΓ hGauss
    have hb := projection_derivative_on_tangent_local
      f π y b c hf2 hπ hfix
    have ha := projection_derivative_on_tangent_local
      f π y a (Γ y b c) hf2 hπ hfix
    have hg := hGaussY b c
    have hgnested := hGaussY a (Γ y b c)
    have hb' : (fderiv ℝ (fderiv ℝ f) y b) c =
        (fderiv ℝ π y b) (fderiv ℝ f y c) +
          (fderiv ℝ f y) (Γ y b c) := by
      rw [← hg] at hb
      exact hb.symm
    rw [hb', map_add] at hj
    rw [← ha] at hj
    rw [← hgnested] at hj
    simp only [map_add]
    have hcancel := congrArg (fun Z : V =>
      Z - (fderiv ℝ π y a) (fderiv ℝ f y (Γ y b c))) hj
    abel_nf at hcancel ⊢
    exact hcancel
  have huv := hOne u v w
  have hvu := hOne v u w
  have hthird := third_derivative_swap_first_two f y u v w hf
  rw [hthird] at huv
  rw [map_sub]
  rw [huv, hvu]
  abel

end
end QuaternionicSymmetry.GeneralImmersionProjectionCurvatureLocal
