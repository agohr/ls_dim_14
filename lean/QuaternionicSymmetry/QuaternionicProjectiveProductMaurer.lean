import QuaternionicSymmetry.QuaternionicProjectiveKernelMaurer

/-! Leibniz rule for the actual scalar-times-symplectic factorization of a
fixed-model tangent gauge. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveProductMaurer

open scoped Quaternion Topology
open QuaternionicManifoldSmoothProductLifts
open QuaternionicUnitScalarIsometries
open VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

def productGauge (S : QuaternionicStructure E)
    (q : X → ℍ) (h : X → E →L[ℝ] E) (x : X) : E →L[ℝ] E :=
  scalarActionLinear S (q x) * h x

omit [Nontrivial E] in
theorem fderiv_scalarAction (S : QuaternionicStructure E)
    (q : X → ℍ) (x : X) (hq : DifferentiableAt ℝ q x) (u : X) :
    fderiv ℝ (fun y => scalarActionLinear S (q y)) x u =
      scalarActionLinear S (fderiv ℝ q x u) := by
  let L : ℍ →L[ℝ] (E →L[ℝ] E) :=
    (scalarActionLinear S).toContinuousLinearMap
  have hc : fderiv ℝ (L ∘ q) x = L.comp (fderiv ℝ q x) := by
    simpa only [L.fderiv] using fderiv_comp x (g := L) L.differentiableAt hq
  exact congrArg (fun F : X →L[ℝ] (E →L[ℝ] E) => F u) hc

omit [Nontrivial E] in
theorem fderiv_productGauge (S : QuaternionicStructure E)
    (q : X → ℍ) (h : X → E →L[ℝ] E) (x u : X)
    (hq : DifferentiableAt ℝ q x)
    (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ (productGauge S q h) x u =
      scalarActionLinear S (q x) * fderiv ℝ h x u +
        scalarActionLinear S (fderiv ℝ q x u) * h x := by
  have hqa : DifferentiableAt ℝ (fun y => scalarActionLinear S (q y)) x :=
    (scalarActionLinear S).toContinuousLinearMap.differentiableAt.comp x hq
  have hd := fderiv_fun_mul' hqa hh
  have he := congrArg (fun F : X →L[ℝ] (E →L[ℝ] E) => F u) hd
  simpa only [productGauge, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, op_smul_eq_mul,
    fderiv_scalarAction S q x hq u] using he

omit [Nontrivial E] in
theorem scalarAction_mul (S : QuaternionicStructure E) (q r : ℍ) :
    scalarActionLinear S (q * r) =
      scalarActionLinear S q * scalarActionLinear S r := by
  apply ContinuousLinearMap.ext
  intro v
  change S.action (q * r) v = S.action q (S.action r v)
  rw [map_mul]
  rfl

omit [Nontrivial E] in
theorem scalarAction_star_mul (S : QuaternionicStructure E) (q r : ℍ) :
    scalarActionLinear S (star q * r) =
      scalarActionLinear S (star q) * scalarActionLinear S r :=
  scalarAction_mul S (star q) r

omit [Nontrivial E] in
theorem scalarAction_one (S : QuaternionicStructure E) :
    scalarActionLinear S (1 : ℍ) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  change S.action (1 : ℍ) v = v
  norm_num

omit [Nontrivial E] in
theorem productGauge_maurer (S : QuaternionicStructure E)
    (q : X → ℍ) (h : X → E →L[ℝ] E) (x u : X)
    (hq : DifferentiableAt ℝ q x)
    (hh : DifferentiableAt ℝ h x)
    (hInv : E →L[ℝ] E)
    (hnorm : star (q x) * q x = 1)
    (hleft : hInv * h x = 1)
    (hcomm : hInv * scalarActionLinear S
        (star (q x) * fderiv ℝ q x u) =
      scalarActionLinear S (star (q x) * fderiv ℝ q x u) * hInv) :
    (hInv * scalarActionLinear S (star (q x))) *
        fderiv ℝ (productGauge S q h) x u =
      scalarActionLinear S (star (q x) * fderiv ℝ q x u) +
        hInv * fderiv ℝ h x u := by
  rw [fderiv_productGauge S q h x u hq hh, mul_add]
  calc
    _ = hInv * (scalarActionLinear S (star (q x)) *
          scalarActionLinear S (q x)) * fderiv ℝ h x u +
        hInv * scalarActionLinear S (star (q x) * fderiv ℝ q x u) * h x := by
      rw [scalarAction_star_mul]
      simp only [mul_assoc]
    _ = _ := by
      rw [← scalarAction_mul, hnorm]
      rw [scalarAction_one, mul_one, hcomm, mul_assoc, hleft, mul_one]
      abel

theorem scalarAction_pure_eq_synth (S : QuaternionicStructure E)
    (p : ℍ) (hp : p.re = 0) :
    scalarActionLinear S p =
      synth S (![p.imI, p.imJ, p.imK] : Fin 3 → ℝ) := by
  let a : Fin 3 → ℝ := ![p.imI, p.imJ, p.imK]
  have ha : pureScalar a = p := by
    ext <;> simp [pureScalar, a, hp]
  apply ContinuousLinearMap.ext
  intro v
  rw [← ha]
  exact action_pureScalar S a v

omit [Nontrivial E] in
theorem productGauge_inverse (S : QuaternionicStructure E)
    (q : ℍ) (h hInv : E →L[ℝ] E)
    (hq₁ : star q * q = 1) (hq₂ : q * star q = 1)
    (hh₁ : hInv * h = 1) (hh₂ : h * hInv = 1) :
    (hInv * scalarActionLinear S (star q)) *
        (scalarActionLinear S q * h) = 1 ∧
      (scalarActionLinear S q * h) *
        (hInv * scalarActionLinear S (star q)) = 1 := by
  constructor
  · rw [mul_assoc, ← mul_assoc (scalarActionLinear S (star q)),
      ← scalarAction_mul, hq₁, scalarAction_one, one_mul, hh₁]
  · rw [mul_assoc, ← mul_assoc h hInv, hh₂, one_mul,
      ← scalarAction_mul, hq₂, scalarAction_one]

theorem productGauge_maurer_of_kernel (S : QuaternionicStructure E)
    (q : X → ℍ) (h : X → E →L[ℝ] E) (x u : X)
    (hq : DifferentiableAt ℝ q x)
    (hh : DifferentiableAt ℝ h x)
    (hunit : ∀ᶠ y in 𝓝 x, star (q y) * q y = 1)
    (hright : q x * star (q x) = 1)
    (hInv : E →L[ℝ] E) (hleft : hInv * h x = 1)
    (hInvC : ∀ a : Fin 3 → ℝ,
      hInv * synth S a = synth S a * hInv) :
    (hInv * scalarActionLinear S (star (q x))) *
        fderiv ℝ (productGauge S q h) x u =
      scalarActionLinear S (star (q x) * fderiv ℝ q x u) +
        hInv * fderiv ℝ h x u := by
  have hpure := QuaternionicProjectiveLineMaurer.star_mul_fderiv_pure
    q x hq hunit hright u
  have hcomm : hInv * scalarActionLinear S
        (star (q x) * fderiv ℝ q x u) =
      scalarActionLinear S (star (q x) * fderiv ℝ q x u) * hInv := by
    rw [scalarAction_pure_eq_synth S _ hpure]
    exact hInvC _
  exact productGauge_maurer S q h x u hq hh hInv hunit.self_of_nhds hleft hcomm

end
end QuaternionicSymmetry.QuaternionicProjectiveProductMaurer
