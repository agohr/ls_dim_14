import QuaternionicSymmetry.QuaternionicManifoldStandardLocalOperator
import QuaternionicSymmetry.QuaternionicProjectiveStandardLieBracket

/-! The differential of the right quaternionic line factor in the standard
representation. These formulas retain the order of quaternion multiplication. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveLineMaurer

open scoped Quaternion ContDiff Topology
open QuaternionicProjectiveStandardLie
open QuaternionicManifoldStandardLocalOperator
open QuaternionicUnitScalarIsometries
open QuaternionicProjectiveStandardLieBracket
open VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

def rightStar (q : ℍ) : ℍ →L[ℝ] ℍ :=
  ((ContinuousLinearMap.mul ℝ ℍ).flip) (star q)

private def starLinear : ℍ →ₗ[ℝ] ℍ where
  toFun := star
  map_add' a b := by simp
  map_smul' r a := by simp [Quaternion.star_smul]

theorem differentiableAt_rightStar {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℍ) (x : X) (hq : DifferentiableAt ℝ q x) :
    DifferentiableAt ℝ (fun y => rightStar (q y)) x := by
  exact (((ContinuousLinearMap.mul ℝ ℍ).flip).differentiableAt.comp x
    (starLinear.toContinuousLinearMap.differentiableAt.comp x hq))

theorem rightStar_fderiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℍ) (x : X) (hq : DifferentiableAt ℝ q x) (u : X) :
    fderiv ℝ (fun y => rightStar (q y)) x u =
      ((ContinuousLinearMap.mul ℝ ℍ).flip) (star (fderiv ℝ q x u)) := by
  let L : ℍ →L[ℝ] (ℍ →L[ℝ] ℍ) :=
    ((ContinuousLinearMap.mul ℝ ℍ).flip).comp
      starLinear.toContinuousLinearMap
  change fderiv ℝ (L ∘ q) x u = L (fderiv ℝ q x u)
  have hc : fderiv ℝ (L ∘ q) x = L.comp (fderiv ℝ q x) := by
    simpa only [L.fderiv] using fderiv_comp x (g := L) L.differentiableAt hq
  rw [hc]
  rfl

theorem rightStar_comp (q r : ℍ) :
    rightStar q * rightStar r = rightStar (q * r) := by
  apply ContinuousLinearMap.ext
  intro w
  change (w * star r) * star q = w * star (q * r)
  rw [star_mul, mul_assoc]

theorem rightStar_one : rightStar 1 = ContinuousLinearMap.id ℝ ℍ := by
  apply ContinuousLinearMap.ext
  intro w
  simp [rightStar]

theorem rightStar_inverse (q : ℍ) (hq : star q * q = 1) (hq' : q * star q = 1) :
    rightStar (star q) * rightStar q = 1 ∧
      rightStar q * rightStar (star q) = 1 := by
  constructor
  · rw [rightStar_comp, hq, rightStar_one]
    rfl
  · rw [rightStar_comp, hq', rightStar_one]
    rfl

theorem rightStar_maurer_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℍ) (x : X) (hq : DifferentiableAt ℝ q x) (u : X) (w : ℍ) :
    (rightStar (star (q x)) *
        fderiv ℝ (fun y => rightStar (q y)) x u) w =
      w * (star (fderiv ℝ q x u) * q x) := by
  rw [rightStar_fderiv q x hq u]
  simp [rightStar, mul_assoc]

theorem fderiv_star {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℍ) (x : X) (hq : DifferentiableAt ℝ q x) (u : X) :
    fderiv ℝ (fun y => star (q y)) x u = star (fderiv ℝ q x u) := by
  let L : ℍ →L[ℝ] ℍ := starLinear.toContinuousLinearMap
  have hc : fderiv ℝ (L ∘ q) x = L.comp (fderiv ℝ q x) := by
    simpa only [L.fderiv] using fderiv_comp x (g := L) L.differentiableAt hq
  have he := congrArg (fun F : X →L[ℝ] ℍ => F u) hc
  exact he

theorem star_fderiv_mul_of_unit {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℍ) (x : X) (hq : DifferentiableAt ℝ q x)
    (hunit : ∀ᶠ y in 𝓝 x, star (q y) * q y = 1)
    (hright : q x * star (q x) = 1) (u : X) :
    star (fderiv ℝ q x u) * q x = -(star (q x) * fderiv ℝ q x u) := by
  have hstar : DifferentiableAt ℝ (fun y => star (q y)) x :=
    starLinear.toContinuousLinearMap.differentiableAt.comp x hq
  have h := LocalConnectionGauge.fderiv_inverse_pair q
    (fun y => star (q y)) x hq hstar hunit hright u
  rw [fderiv_star q x hq u] at h
  have hleftx : star (q x) * q x = 1 := hunit.self_of_nhds
  calc
    _ = (-(star (q x) * fderiv ℝ q x u * star (q x))) * q x := by rw [h]
    _ = _ := by rw [neg_mul, mul_assoc, mul_assoc, hleftx, mul_one]

theorem star_mul_fderiv_pure {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℍ) (x : X) (hq : DifferentiableAt ℝ q x)
    (hunit : ∀ᶠ y in 𝓝 x, star (q y) * q y = 1)
    (hright : q x * star (q x) = 1) (u : X) :
    (star (q x) * fderiv ℝ q x u).re = 0 := by
  apply Quaternion.star_eq_neg.mp
  rw [star_mul, star_star]
  exact star_fderiv_mul_of_unit q x hq hunit hright u

theorem scalarLineLie_scalarAction_pure {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (S : QuaternionicStructure E) (p : ℍ) (hp : p.re = 0) (w : ℍ) :
    scalarLineLie S (QuaternionicManifoldSmoothProductLifts.scalarActionLinear S p) w =
      w * -p := by
  let a : Fin 3 → ℝ := ![p.imI, p.imJ, p.imK]
  have ha : pureScalar a = p := by
    ext <;> simp [pureScalar, a, hp]
  have him : imaginary a = p := by
    ext <;> simp [a, hp]
  have hs : QuaternionicManifoldSmoothProductLifts.scalarActionLinear S p =
      synth S a := by
    ext v
    rw [← ha]
    exact action_pureScalar S a v
  rw [hs, scalarLineLie_synth, him]

theorem rightStar_maurer_eq_scalarLineLie {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : QuaternionicStructure E) (q : X → ℍ) (x : X)
    (hq : DifferentiableAt ℝ q x)
    (hunit : ∀ᶠ y in 𝓝 x, star (q y) * q y = 1)
    (hright : q x * star (q x) = 1) (u : X) :
    rightStar (star (q x)) * fderiv ℝ (fun y => rightStar (q y)) x u =
      scalarLineLie S (QuaternionicManifoldSmoothProductLifts.scalarActionLinear S
        (star (q x) * fderiv ℝ q x u)) := by
  apply ContinuousLinearMap.ext
  intro w
  rw [rightStar_maurer_apply q x hq u w,
    star_fderiv_mul_of_unit q x hq hunit hright u,
    scalarLineLie_scalarAction_pure S _
      (star_mul_fderiv_pure q x hq hunit hright u) w]

end
end QuaternionicSymmetry.QuaternionicProjectiveLineMaurer
