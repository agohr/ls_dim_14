import QuaternionicSymmetry.LocalConnectionExterior
import QuaternionicSymmetry.LocalConnectionGauge
import QuaternionicSymmetry.DifferentialFormCoefficient

/-! Local Chern--Weil calculus for invariant linear functionals. The forms,
their exterior derivatives, and the transgression one-form are actual
continuous alternating forms. Cyclicity is an explicit algebraic premise;
the endomorphism-trace instance is constructed separately. -/

namespace QuaternionicSymmetry.LocalChernWeilLinear

open LocalConnection LocalConnectionForms LocalConnectionExterior LocalConnectionGauge
  DifferentialFormCoefficient ContinuousAlternatingMap
open scoped Topology

noncomputable section

variable {E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]

def characteristicForm (T : A →L[ℝ] B) (Γ : Form (E := E) (A := A)) :
    E → E [⋀^Fin 2]→L[ℝ] B := mapForm T (curvatureForm Γ)

theorem characteristicForm_apply (T : A →L[ℝ] B) (Γ : Form (E := E) (A := A))
    (x : E) (v : Fin 2 → E) :
    characteristicForm T Γ x v = T (curvature Γ x (v 0) (v 1)) := by
  rw [characteristicForm, mapForm_apply, curvatureForm_apply]

theorem cyclic_commutatorForm (T : A →L[ℝ] B) (hT : ∀ a b, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := A)) (F : E [⋀^Fin 2]→L[ℝ] A) (x : E) :
    T.compContinuousAlternatingMap (commutatorForm Γ F x) = 0 := by
  ext v
  change T (commutatorForm Γ F x v) = 0
  rw [commutatorForm_apply]
  simp only [map_add, map_sub]
  rw [hT (Γ x (v 0)), hT (Γ x (v 1)), hT (Γ x (v 2))]
  abel

theorem closed (T : A →L[ℝ] B) (hT : ∀ a b, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := A)) (x : E) (hΓ : ContDiffAt ℝ 2 Γ x) :
    extDeriv (characteristicForm T Γ) x = 0 := by
  have h₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [characteristicForm, extDeriv_mapForm T _ x
    (differentiableAt_curvatureForm Γ x h₁ h₂)]
  have hb := bianchi_form Γ x hΓ
  have ht := congrArg ((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E A B) T) hb
  rw [map_add, _root_.map_zero] at ht
  change T.compContinuousAlternatingMap (extDeriv (curvatureForm Γ) x) +
    T.compContinuousAlternatingMap (commutatorForm Γ (curvatureForm Γ x) x) = 0 at ht
  simpa only [cyclic_commutatorForm T hT, add_zero] using ht

theorem characteristicForm_eq_extDeriv (T : A →L[ℝ] B)
    (hT : ∀ a b, T (a * b) = T (b * a)) (Γ : Form (E := E) (A := A))
    (x : E) (hΓ : DifferentiableAt ℝ Γ x) :
    characteristicForm T Γ x = extDeriv (mapForm T (connectionForm Γ)) x := by
  have hc : DifferentiableAt ℝ (connectionForm Γ) x :=
    (oneFormMap (E := E) (A := A)).differentiableAt.comp x hΓ
  rw [extDeriv_mapForm T _ x hc, extDeriv_connectionForm Γ x hΓ]
  ext v
  change characteristicForm T Γ x v = T (alternatingPart (fderiv ℝ Γ x) v)
  rw [characteristicForm_apply, alternatingPart_apply, curvature_apply]
  simp only [map_add, map_sub]
  rw [hT (Γ x (v 0))]
  abel

theorem transgression (T : A →L[ℝ] B) (hT : ∀ a b, T (a * b) = T (b * a))
    (Γ₀ Γ₁ : Form (E := E) (A := A)) (x : E)
    (h₀ : DifferentiableAt ℝ Γ₀ x) (h₁ : DifferentiableAt ℝ Γ₁ x) :
    characteristicForm T Γ₁ x - characteristicForm T Γ₀ x =
      extDeriv (mapForm T (connectionForm (Γ₁ - Γ₀))) x := by
  rw [← characteristicForm_eq_extDeriv T hT (Γ₁ - Γ₀) x (h₁.sub h₀)]
  ext v
  simp only [ContinuousAlternatingMap.sub_apply, characteristicForm_apply, curvature_apply,
    fderiv_sub h₁ h₀, Pi.sub_apply, ContinuousLinearMap.sub_apply, map_sub, map_add]
  rw [hT (Γ₁ x (v 0)), hT (Γ₀ x (v 0)), hT (Γ₁ x (v 0) - Γ₀ x (v 0))]
  abel

theorem gauge_invariant (T : A →L[ℝ] B) (hT : ∀ a b, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := A)) (g h : E → A) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1) (hright : g x * h x = 1) :
    characteristicForm T (transform Γ g h) x = characteristicForm T Γ x := by
  ext v
  simp only [characteristicForm_apply, curvature_transform Γ g h x hΓ hg hh hleft hright]
  rw [hT, ← mul_assoc, hright, one_mul]

end
end QuaternionicSymmetry.LocalChernWeilLinear
