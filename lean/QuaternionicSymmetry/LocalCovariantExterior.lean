import QuaternionicSymmetry.LocalConnectionExterior
import QuaternionicSymmetry.LocalConnectionGauge
import QuaternionicSymmetry.DifferentialFormCoefficient

/-! Covariant exterior differentiation in every degree. The definition uses
the actual exterior derivative and alternation of the coefficient commutator. -/

namespace QuaternionicSymmetry.LocalCovariantExterior

open LocalConnection LocalConnectionForms LocalConnectionGauge DifferentialFormCoefficient
  ContinuousAlternatingMap
open scoped Topology

noncomputable section

variable {E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  {n : ℕ}

local instance : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A
local instance : NormedAddCommGroup (A →L[ℝ] A) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (A →L[ℝ] A) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E [⋀^Fin n]→L[ℝ] A) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin n]→L[ℝ] A) := inferInstance

def commutator (Γ : Form (E := E) (A := A)) (ω : E [⋀^Fin n]→L[ℝ] A) (x : E) :
    E [⋀^Fin (n + 1)]→L[ℝ] A :=
  alternatizeUncurryFin
    (((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E A A).flip ω).comp
      (((ContinuousLinearMap.mul ℝ A) - (ContinuousLinearMap.mul ℝ A).flip).comp (Γ x)))

theorem commutator_apply (Γ : Form (E := E) (A := A)) (ω : E [⋀^Fin n]→L[ℝ] A)
    (x : E) (v : Fin (n + 1) → E) :
    commutator Γ ω x v = ∑ i, (-1 : ℤ) ^ i.val •
      (Γ x (v i) * ω (i.removeNth v) - ω (i.removeNth v) * Γ x (v i)) := by
  simp [commutator, alternatizeUncurryFin_apply]

def covariantExteriorDerivative (Γ : Form (E := E) (A := A))
    (ω : E → E [⋀^Fin n]→L[ℝ] A) (x : E) : E [⋀^Fin (n + 1)]→L[ℝ] A :=
  extDeriv ω x + commutator Γ (ω x) x

theorem covariantExteriorDerivative_apply (Γ : Form (E := E) (A := A))
    (ω : E → E [⋀^Fin n]→L[ℝ] A) (x : E) (hω : DifferentiableAt ℝ ω x)
    (v : Fin (n + 1) → E) :
    covariantExteriorDerivative Γ ω x v = ∑ i, (-1 : ℤ) ^ i.val •
      (fderiv ℝ (fun y => ω y (i.removeNth v)) x (v i) +
        Γ x (v i) * ω x (i.removeNth v) - ω x (i.removeNth v) * Γ x (v i)) := by
  simp only [covariantExteriorDerivative, ContinuousAlternatingMap.add_apply,
    extDeriv_apply hω, commutator_apply, smul_sub, smul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  abel

theorem cyclic_commutator (T : A →L[ℝ] B) (hT : ∀ a b, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := A)) (ω : E [⋀^Fin n]→L[ℝ] A) (x : E) :
    T.compContinuousAlternatingMap (commutator Γ ω x) = 0 := by
  ext v
  change T (commutator Γ ω x v) = 0
  rw [commutator_apply, _root_.map_sum]
  apply Finset.sum_eq_zero
  intro i _
  simp only [map_zsmul, map_sub, hT (Γ x (v i)), sub_self, smul_zero]

theorem cyclic_covariantExteriorDerivative (T : A →L[ℝ] B)
    (hT : ∀ a b, T (a * b) = T (b * a)) (Γ : Form (E := E) (A := A))
    (ω : E → E [⋀^Fin n]→L[ℝ] A) (x : E) (hω : DifferentiableAt ℝ ω x) :
    T.compContinuousAlternatingMap (covariantExteriorDerivative Γ ω x) =
      extDeriv (mapForm T ω) x := by
  rw [extDeriv_mapForm T ω x hω]
  have hc := cyclic_commutator T hT Γ (ω x) x
  ext v
  have hv := congrArg (fun f : E [⋀^Fin (n + 1)]→L[ℝ] B => f v) hc
  change T (commutator Γ (ω x) x v) = 0 at hv
  change T (extDeriv ω x v + commutator Γ (ω x) x v) = T (extDeriv ω x v)
  rw [map_add, hv, add_zero]

theorem bianchi (Γ : Form (E := E) (A := A)) (x : E) (hΓ : ContDiffAt ℝ 2 Γ x) :
    covariantExteriorDerivative Γ (curvatureForm Γ) x = 0 :=
  LocalConnectionExterior.bianchi_form Γ x hΓ

theorem covariantExteriorDerivative_connectionForm (Γ θ : Form (E := E) (A := A))
    (x : E) (hθ : DifferentiableAt ℝ θ x) :
    covariantExteriorDerivative Γ (connectionForm θ) x = covariantDerivativeForm Γ θ x := by
  ext v
  rw [LocalConnectionForms.covariantDerivativeForm_apply Γ θ x v]
  simp only [covariantExteriorDerivative, ContinuousAlternatingMap.add_apply,
    extDeriv_connectionForm θ x hθ, alternatingPart_apply, commutator_apply,
    covariantDerivative_apply]
  simp [Fin.sum_univ_two, connectionForm, oneFormMap_apply, Fin.removeNth]
  noncomm_ring

def adjoint (ω : E → E [⋀^Fin n]→L[ℝ] A) (g h : E → A) :
    E → E [⋀^Fin n]→L[ℝ] A := fun x =>
  (((ContinuousLinearMap.mul ℝ A) (h x)).comp
    ((ContinuousLinearMap.mul ℝ A).flip (g x))).compContinuousAlternatingMap (ω x)

theorem adjoint_apply (ω : E → E [⋀^Fin n]→L[ℝ] A) (g h : E → A)
    (x : E) (v : Fin n → E) : adjoint ω g h x v = h x * (ω x v * g x) := rfl

theorem adjoint_one (ω : E → E [⋀^Fin n]→L[ℝ] A) :
    adjoint ω (fun _ => 1) (fun _ => 1) = ω := by
  funext x
  ext v
  simp [adjoint_apply]

theorem adjoint_neg (ω : E → E [⋀^Fin n]→L[ℝ] A) (g h : E → A) :
    adjoint ω (-g) (-h) = adjoint ω g h := by
  funext x
  ext v
  simp [adjoint_apply]

theorem adjoint_comp (ω : E → E [⋀^Fin n]→L[ℝ] A) (g₁ h₁ g₂ h₂ : E → A) :
    adjoint (adjoint ω g₁ h₁) g₂ h₂ =
      adjoint ω (fun y => g₁ y * g₂ y) (fun y => h₂ y * h₁ y) := by
  funext x
  ext v
  simp only [adjoint_apply, mul_assoc]

theorem adjoint_connectionForm (θ : Form (E := E) (A := A)) (g h : E → A) :
    adjoint (connectionForm θ) g h = connectionForm (adjointForm θ g h) := by
  funext x
  ext v
  rfl

theorem cyclic_adjoint (T : A →L[ℝ] B) (hT : ∀ a b, T (a * b) = T (b * a))
    (ω : E → E [⋀^Fin n]→L[ℝ] A) (g h : E → A) (x : E) (hright : g x * h x = 1) :
    mapForm T (adjoint ω g h) x = mapForm T ω x := by
  ext v
  simp only [mapForm_apply, adjoint_apply]
  rw [hT, mul_assoc, hright, mul_one]

theorem differentiableAt_adjoint (ω : E → E [⋀^Fin n]→L[ℝ] A) (g h : E → A) (x : E)
    (hω : DifferentiableAt ℝ ω x) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) : DifferentiableAt ℝ (adjoint ω g h) x := by
  have hc : DifferentiableAt ℝ (fun y => ((ContinuousLinearMap.mul ℝ A) (h y)).comp
      ((ContinuousLinearMap.mul ℝ A).flip (g y))) x :=
    ((ContinuousLinearMap.mul ℝ A).differentiableAt.comp x hh).clm_comp
    ((ContinuousLinearMap.mul ℝ A).flip.differentiableAt.comp x hg)
  have hl : DifferentiableAt ℝ (fun y =>
      (ContinuousLinearMap.compContinuousAlternatingMapCLM (ι := Fin n) ℝ E A A)
        (((ContinuousLinearMap.mul ℝ A) (h y)).comp
          ((ContinuousLinearMap.mul ℝ A).flip (g y)))) x :=
    (ContinuousLinearMap.compContinuousAlternatingMapCLM (ι := Fin n) ℝ E A A).differentiableAt.comp x hc
  exact hl.clm_apply hω

theorem fderiv_adjoint_apply (ω : E → E [⋀^Fin n]→L[ℝ] A) (g h : E → A) (x : E)
    (hω : DifferentiableAt ℝ ω x) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) (v : Fin n → E) (u : E) :
    fderiv ℝ (fun y => adjoint ω g h y v) x u =
      h x * (ω x v * fderiv ℝ g x u + fderiv ℝ (fun y => ω y v) x u * g x) +
        fderiv ℝ h x u * (ω x v * g x) := by
  have hv := hω.continuousAlternatingMap_apply_const v
  have hd := (hh.hasFDerivAt.mul' (hv.hasFDerivAt.mul' hg.hasFDerivAt)).fderiv
  change fderiv ℝ (fun y => h y * (ω y v * g y)) x = _ at hd
  simp only [adjoint_apply]
  rw [hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, op_smul_eq_mul]
  rfl

theorem covariantExteriorDerivative_adjoint (Γ : Form (E := E) (A := A))
    (ω : E → E [⋀^Fin n]→L[ℝ] A) (g h : E → A) (x : E)
    (hω : DifferentiableAt ℝ ω x) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1) (hright : g x * h x = 1) :
    covariantExteriorDerivative (transform Γ g h) (adjoint ω g h) x =
      adjoint (covariantExteriorDerivative Γ ω) g h x := by
  ext v
  rw [covariantExteriorDerivative_apply _ _ x (differentiableAt_adjoint ω g h x hω hg hh),
    adjoint_apply, covariantExteriorDerivative_apply Γ ω x hω]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [fderiv_adjoint_apply ω g h x hω hg hh, transform_apply, adjoint_apply,
    fderiv_inverse_pair g h x hg hh hleft hright]
  have hc (a : A) : g x * (h x * a) = a := by rw [← mul_assoc, hright, one_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_assoc, hc]
  noncomm_ring

end
end QuaternionicSymmetry.LocalCovariantExterior
