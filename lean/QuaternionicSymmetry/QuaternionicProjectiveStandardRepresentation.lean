import QuaternionicSymmetry.QuaternionicManifoldSignedLocalLifts
import QuaternionicSymmetry.QuaternionicLine

/-! The actual quaternion-linear standard representation of
`Sp(E) × Sp(1)` on `E ⊕ ℍ`. The quaternion line has left `i,j` actions,
so its commuting `Sp(1)` factor acts by right multiplication by `star q`.
This reversal makes the action a group homomorphism. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveStandardRepresentation

open scoped Quaternion
open QuaternionicIsometryNormalizer QuaternionicUnitScalarIsometries
  QuaternionicUnitQuaternionTransport

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
variable (S : QuaternionicStructure E)

def rightStarEquiv (q : unitary ℍ) : ℍ ≃L[ℝ] ℍ where
  toFun w := w * star (q : ℍ)
  invFun w := w * (q : ℍ)
  map_add' a b := add_mul a b _
  map_smul' r w := by simp [Algebra.smul_def, mul_assoc]
  left_inv w := by
    have hs : star (q : ℍ) * (q : ℍ) = 1 :=
      (Unitary.mem_iff.mp q.property).1
    simp [mul_assoc, hs]
  right_inv w := by
    have hs : (q : ℍ) * star (q : ℍ) = 1 :=
      (Unitary.mem_iff.mp q.property).2
    simp [mul_assoc, hs]
  continuous_toFun :=
    (((ContinuousLinearMap.mul ℝ ℍ).flip) (star (q : ℍ))).continuous
  continuous_invFun :=
    (((ContinuousLinearMap.mul ℝ ℍ).flip) (q : ℍ)).continuous

@[simp] theorem rightStarEquiv_apply (q : unitary ℍ) (w : ℍ) :
    rightStarEquiv q w = w * star (q : ℍ) := rfl

theorem rightStarEquiv_mul (q r : unitary ℍ) :
    rightStarEquiv (q * r) = rightStarEquiv q * rightStarEquiv r := by
  apply ContinuousLinearEquiv.ext
  funext w
  change w * star ((q * r : unitary ℍ) : ℍ) =
    (w * star (r : ℍ)) * star (q : ℍ)
  simp [star_mul, mul_assoc]

def standardAction :
    (symplecticKernel S × unitary ℍ) →* ((E × ℍ) ≃L[ℝ] (E × ℍ)) where
  toFun p := p.1.1.1.toContinuousLinearEquiv.prodCongr (rightStarEquiv p.2)
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext z
    rcases z with ⟨v, w⟩
    change (v, w * star (1 : ℍ)) = (v, w)
    simp
  map_mul' p r := by
    apply ContinuousLinearEquiv.ext
    funext z
    rcases z with ⟨v, w⟩
    change ((p.1.1.1 * r.1.1.1) v,
      w * star (((p.2 * r.2 : unitary ℍ) : ℍ))) =
      (p.1.1.1 (r.1.1.1 v), (w * star (r.2 : ℍ)) * star (p.2 : ℍ))
    simp [star_mul, mul_assoc]

@[simp] theorem standardAction_apply (p : symplecticKernel S × unitary ℍ)
    (v : E) (w : ℍ) :
    standardAction S p (v, w) = (p.1.1.1 v, w * star (p.2 : ℍ)) := rfl

/-- Both blocks commute with left quaternionic multiplication, so the
representation lies in the quaternionic-linear unitary group. -/
theorem standardAction_commutes_leftI
    (p : symplecticKernel S × unitary ℍ) (v : E) (w : ℍ) :
    standardAction S p (S.I v, QuaternionicLine.unitI * w) =
      (S.I (standardAction S p (v, w)).1,
        QuaternionicLine.unitI * (standardAction S p (v, w)).2) := by
  have hp := (mem_symplecticKernel_iff S p.1.1).mp p.1.2
  simp only [standardAction_apply, hp.1, mul_assoc]

theorem standardAction_commutes_leftJ
    (p : symplecticKernel S × unitary ℍ) (v : E) (w : ℍ) :
    standardAction S p (S.J v, QuaternionicLine.unitJ * w) =
      (S.J (standardAction S p (v, w)).1,
        QuaternionicLine.unitJ * (standardAction S p (v, w)).2) := by
  have hp := (mem_symplecticKernel_iff S p.1.1).mp p.1.2
  simp only [standardAction_apply, hp.2, mul_assoc]

theorem rightStarEquiv_norm (q : unitary ℍ) (w : ℍ) :
    ‖rightStarEquiv q w‖ = ‖w‖ := by
  have hq : ‖(q : ℍ)‖ = 1 := by
    have hs := Quaternion.normSq_eq_norm_mul_self (q : ℍ)
    rw [normSq_one_of_unitary] at hs
    nlinarith [norm_nonneg (q : ℍ)]
  rw [rightStarEquiv_apply, norm_mul, norm_star, hq, mul_one]

theorem standardAction_norm (p : symplecticKernel S × unitary ℍ)
    (z : E × ℍ) : ‖standardAction S p z‖ = ‖z‖ := by
  rcases z with ⟨v, w⟩
  simp only [standardAction_apply, Prod.norm_def]
  rw [p.1.1.1.norm_map]
  exact congrArg (max ‖v‖) (by
    simpa only [rightStarEquiv_apply] using rightStarEquiv_norm p.2 w)

def standardIsometry :
    (symplecticKernel S × unitary ℍ) →* ((E × ℍ) ≃ₗᵢ[ℝ] (E × ℍ)) where
  toFun p := LinearIsometryEquiv.mk
    (standardAction S p).toLinearEquiv (standardAction_norm S p)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro z
    change standardAction S 1 z = z
    rw [map_one]
    rfl
  map_mul' p r := by
    apply LinearIsometryEquiv.ext
    intro z
    change standardAction S (p * r) z =
      standardAction S p (standardAction S r z)
    rw [map_mul]
    rfl

@[simp] theorem standardIsometry_apply
    (p : symplecticKernel S × unitary ℍ) (z : E × ℍ) :
    standardIsometry S p z = standardAction S p z := rfl

/-- The kernel of the tangent `Sp(n)·Sp(1)` action is sent to the common
central sign on the two blocks of the standard representation. -/
theorem standardAction_kernel_sign
    (p : symplecticKernel S × unitary ℍ)
    (hp : symplecticProductAction S p = 1) :
    (((p.2 : ℍ) = 1) ∧ ∀ z : E × ℍ, standardAction S p z = z) ∨
    (((p.2 : ℍ) = -1) ∧ ∀ z : E × ℍ, standardAction S p z = -z) := by
  have hh : p.1.1 = (unitQuaternionNormalizerAction S p.2)⁻¹ := by
    have h := hp
    change p.1.1 * unitQuaternionNormalizerAction S p.2 = 1 at h
    calc
      p.1.1 = p.1.1 * unitQuaternionNormalizerAction S p.2 *
          (unitQuaternionNormalizerAction S p.2)⁻¹ := by group
      _ = (unitQuaternionNormalizerAction S p.2)⁻¹ := by rw [h]; simp
  have htop (v : E) : p.1.1.1 v = S.action (star (p.2 : ℍ)) v := by
    rw [hh]
    rfl
  rcases symplecticProduct_kernel_sign S p hp with hq | hq
  · refine Or.inl ⟨hq, ?_⟩
    intro z
    rcases z with ⟨v, w⟩
    simp only [standardAction_apply]
    apply Prod.ext
    · rw [htop, hq]
      norm_num
    · rw [hq]
      simp
  · refine Or.inr ⟨hq, ?_⟩
    intro z
    rcases z with ⟨v, w⟩
    simp only [standardAction_apply]
    apply Prod.ext
    · rw [htop, hq]
      simp
    · rw [hq]
      simp

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardRepresentation
