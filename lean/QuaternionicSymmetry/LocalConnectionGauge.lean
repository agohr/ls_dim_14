import QuaternionicSymmetry.LocalConnectionBianchi

/-! Gauge transformation of local connections and curvature. Inverse gauge
maps are required only on a neighborhood of the point of calculation. -/

namespace QuaternionicSymmetry.LocalConnectionGauge

open LocalConnection LocalConnectionBianchi
open scoped Topology

noncomputable section

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

theorem fderiv_inverse_pair (g h : E → A) (x : E)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (u : E) :
    fderiv ℝ h x u = -(h x * fderiv ℝ g x u * h x) := by
  have hd := hleft.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_mul' hh hg] at hd
  have hzero : fderiv ℝ (fun _ : E => (1 : A)) x = 0 :=
    (hasFDerivAt_const (1 : A) x).fderiv
  rw [hzero] at hd
  have he := congrArg (fun L : E →L[ℝ] A => L u) hd
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, op_smul_eq_mul, ContinuousLinearMap.zero_apply] at he
  have he' : fderiv ℝ h x u * g x = -(h x * fderiv ℝ g x u) := by
    calc
      _ = (h x * fderiv ℝ g x u + fderiv ℝ h x u * g x) - h x * fderiv ℝ g x u := by abel
      _ = _ := by rw [he]; simp
  calc
    _ = (fderiv ℝ h x u * g x) * h x := by rw [mul_assoc, hright, mul_one]
    _ = _ := by rw [he', neg_mul]

def transform (Γ : Form (E := E) (A := A)) (g h : E → A) : Form (E := E) (A := A) :=
  fun x => ((ContinuousLinearMap.mul ℝ A) (h x)).comp
    (((ContinuousLinearMap.mul ℝ A).flip (g x)).comp (Γ x) + fderiv ℝ g x)

theorem transform_apply (Γ : Form (E := E) (A := A)) (g h : E → A) (x v : E) :
    transform Γ g h x v = h x * (Γ x v * g x + fderiv ℝ g x v) := rfl

theorem differentiableAt_transform (Γ : Form (E := E) (A := A)) (g h : E → A) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) (hD : DifferentiableAt ℝ (fderiv ℝ g) x) :
    DifferentiableAt ℝ (transform Γ g h) x :=
  (((ContinuousLinearMap.mul ℝ A).differentiableAt.comp x hh).clm_comp
    ((((ContinuousLinearMap.mul ℝ A).flip.differentiableAt.comp x hg).clm_comp hΓ).add hD))

theorem fderiv_transform_apply (Γ : Form (E := E) (A := A)) (g h : E → A) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) (hD : DifferentiableAt ℝ (fderiv ℝ g) x) (u v : E) :
    fderiv ℝ (transform Γ g h) x u v =
      h x * (Γ x v * fderiv ℝ g x u + fderiv ℝ Γ x u v * g x +
        fderiv ℝ (fderiv ℝ g) x u v) +
      fderiv ℝ h x u * (Γ x v * g x + fderiv ℝ g x v) := by
  have hv : DifferentiableAt ℝ (fun y => Γ y v) x := hΓ.clm_apply (differentiableAt_const _)
  have hDv : DifferentiableAt ℝ (fun y => fderiv ℝ g y v) x :=
    hD.clm_apply (differentiableAt_const _)
  rw [← fderiv_eval_const (differentiableAt_transform Γ g h x hΓ hg hh hD) v u]
  simp_rw [transform_apply]
  have hd := (hh.hasFDerivAt.mul'
    ((hv.hasFDerivAt.mul' hg.hasFDerivAt).add hDv.hasFDerivAt)).fderiv
  change fderiv ℝ (fun y => h y * (Γ y v * g y + fderiv ℝ g y v)) x = _ at hd
  rw [hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, op_smul_eq_mul, fderiv_eval_const hD, fderiv_eval_const hΓ]
  rfl

theorem curvature_transform (Γ : Form (E := E) (A := A)) (g h : E → A) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (v w : E) :
    curvature (transform Γ g h) x v w = h x * curvature Γ x v w * g x := by
  have hg₁ : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hg₂ : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hs := hg.isSymmSndFDerivAt (by norm_num)
  have hcancel (a : A) : g x * (h x * a) = a := by rw [← mul_assoc, hright, one_mul]
  simp only [curvature_apply, fderiv_transform_apply Γ g h x hΓ hg₁ hh hg₂,
    transform_apply, fderiv_inverse_pair g h x hg₁ hh hleft hright]
  rw [hs.eq w v]
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_assoc, hcancel]
  noncomm_ring

def adjointForm (θ : Form (E := E) (A := A)) (g h : E → A) : Form (E := E) (A := A) :=
  fun x => ((ContinuousLinearMap.mul ℝ A) (h x)).comp
    (((ContinuousLinearMap.mul ℝ A).flip (g x)).comp (θ x))

theorem adjointForm_apply (θ : Form (E := E) (A := A)) (g h : E → A) (x v : E) :
    adjointForm θ g h x v = h x * (θ x v * g x) := rfl

theorem transform_path (Γ θ : Form (E := E) (A := A)) (g h : E → A) (t : ℝ) :
    transform (Γ + t • θ) g h = transform Γ g h + t • adjointForm θ g h := by
  funext x
  ext v
  simp only [transform_apply, adjointForm_apply, Pi.add_apply, Pi.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm]
  abel

theorem transform_neg (Γ : Form (E := E) (A := A)) (g h : E → A) :
    transform Γ (-g) (-h) = transform Γ g h := by
  funext x
  ext v
  simp [transform_apply, fderiv_neg, mul_add]

theorem adjointForm_neg (θ : Form (E := E) (A := A)) (g h : E → A) :
    adjointForm θ (-g) (-h) = adjointForm θ g h := by
  funext x
  ext v
  simp [adjointForm_apply]

theorem transform_one (Γ : Form (E := E) (A := A)) :
    transform Γ (fun _ => 1) (fun _ => 1) = Γ := by
  funext x
  ext v
  simp [transform_apply]

theorem transform_comp (Γ : Form (E := E) (A := A)) (g₁ h₁ g₂ h₂ : E → A) (x : E)
    (hg₁ : DifferentiableAt ℝ g₁ x) (hg₂ : DifferentiableAt ℝ g₂ x)
    (h₁g₁ : h₁ x * g₁ x = 1) :
    transform (transform Γ g₁ h₁) g₂ h₂ x =
      transform Γ (fun y => g₁ y * g₂ y) (fun y => h₂ y * h₁ y) x := by
  ext v
  simp only [transform_apply, fderiv_fun_mul' hg₁ hg₂, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, op_smul_eq_mul]
  have hc (a : A) : h₁ x * (g₁ x * a) = a := by rw [← mul_assoc, h₁g₁, one_mul]
  simp only [mul_add, add_mul, mul_assoc, hc]
  abel

end
end QuaternionicSymmetry.LocalConnectionGauge
