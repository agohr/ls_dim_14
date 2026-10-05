import QuaternionicSymmetry.QuaternionicIsometryNormalizer
import QuaternionicSymmetry.QuaternionicAction

/-! Unit quaternions act by genuine orthogonal transformations on every
quaternionic real inner-product space. -/

namespace QuaternionicSymmetry.QuaternionicUnitScalarIsometries

open scoped Quaternion
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicRankThreeOrthogonal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (S : QuaternionicStructure E)

theorem action_star_adjoint (q : ℍ) (v w : E) :
    inner ℝ (S.action q v) w = inner ℝ v (S.action (star q) w) := by
  simp only [S.action_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, S.I_skew, S.J_skew, S.K_skew]
  simp only [Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star,
    starRingEnd_apply, star_trivial]
  ring

theorem action_star_inverse (q : ℍ) (hq : Quaternion.normSq q = 1)
    (v : E) : S.action (star q) (S.action q v) = v := by
  change (S.action (star q) * S.action q) v = v
  rw [← map_mul, Quaternion.star_mul_self, hq]
  norm_num

theorem action_inverse_star (q : ℍ) (hq : Quaternion.normSq q = 1)
    (v : E) : S.action q (S.action (star q) v) = v := by
  change (S.action q * S.action (star q)) v = v
  rw [← map_mul, Quaternion.self_mul_star, hq]
  norm_num

/-- The scalar action of a unit quaternion, as an orthogonal equivalence. -/
def unitScalarIsometry (q : ℍ) (hq : Quaternion.normSq q = 1) : E ≃ₗᵢ[ℝ] E where
  toFun := S.action q
  invFun := S.action (star q)
  map_add' := (S.action q).map_add
  map_smul' := (S.action q).map_smul
  left_inv := action_star_inverse S q hq
  right_inv := action_inverse_star S q hq
  norm_map' v := by
    change ‖S.action q v‖ = ‖v‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    rw [action_star_adjoint S, action_star_inverse S q hq]

@[simp] theorem unitScalarIsometry_apply (q : ℍ)
    (hq : Quaternion.normSq q = 1) (v : E) :
    unitScalarIsometry S q hq v = S.action q v := rfl

theorem normSq_one_of_unitary (q : unitary ℍ) :
    Quaternion.normSq (q : ℍ) = 1 := by
  have h := (Unitary.mem_iff.mp q.property).1
  rw [Quaternion.star_mul_self] at h
  exact congrArg (fun z : ℍ => z.re) h

/-- The genuine unit-quaternion group acts orthogonally on every quaternionic
inner-product space via the existing quaternion algebra action. -/
def unitQuaternionAction : unitary ℍ →* (E ≃ₗᵢ[ℝ] E) where
  toFun q := unitScalarIsometry S q (normSq_one_of_unitary q)
  map_one' := by
    ext v
    change S.action (1 : ℍ) v = v
    norm_num
  map_mul' q r := by
    ext v
    change S.action ((q * r : unitary ℍ) : ℍ) v =
      S.action (q : ℍ) (S.action (r : ℍ) v)
    rw [Submonoid.coe_mul, map_mul]
    rfl

variable [Nontrivial E] [FiniteDimensional ℝ E]

/-- The pure imaginary quaternion with the three given coefficients. -/
def pureScalar (a : Fin 3 → ℝ) : ℍ :=
  ⟨0, a 0, a 1, a 2⟩

@[simp] theorem pureScalar_re (a : Fin 3 → ℝ) : (pureScalar a).re = 0 := rfl

omit [FiniteDimensional ℝ E] in
theorem action_pureScalar (a : Fin 3 → ℝ) (v : E) :
    S.action (pureScalar a) v = (synth S a) v := by
  rw [S.action_apply, synth_apply]
  simp [pureScalar, Fin.sum_univ_succ, quaternionicGenerator]
  abel

theorem action_imaginary_mem (q : ℍ) (hq : q.re = 0) :
    Module.End.toContinuousLinearMap E (S.action q) ∈ quaternionicSpan S := by
  let a : Fin 3 → ℝ := ![q.imI, q.imJ, q.imK]
  have hp : pureScalar a = q := by
    ext <;> simp [pureScalar, a, hq]
  convert synth_mem S a using 1
  ext v
  rw [← hp]
  change S.action (pureScalar a) v = (synth S a) v
  exact action_pureScalar S a v

theorem conjugate_imaginary (q p : ℍ) (hp : p.re = 0) :
    (q * p * star q).re = 0 := by
  apply Quaternion.star_eq_neg.mp
  have hstar : star p = -p := Quaternion.star_eq_neg.mpr hp
  simp only [star_mul, star_star, hstar]
  simp only [mul_neg, neg_mul, mul_assoc]

theorem unitScalar_conjugation (q : ℍ) (hq : Quaternion.normSq q = 1)
    (a : Fin 3 → ℝ) :
    QuaternionicIsometryNormalizer.conjugation
      (unitScalarIsometry S q hq) (synth S a) =
      Module.End.toContinuousLinearMap E
        (S.action (q * pureScalar a * star q)) := by
  ext v
  change S.action q (synth S a (S.action (star q) v)) =
    S.action (q * pureScalar a * star q) v
  rw [← action_pureScalar S a, map_mul, map_mul]
  rfl

theorem unitScalar_preserves_span (q : ℍ) (hq : Quaternion.normSq q = 1)
    (A : E →L[ℝ] E) (hA : A ∈ quaternionicSpan S) :
    QuaternionicIsometryNormalizer.conjugation
      (unitScalarIsometry S q hq) A ∈ quaternionicSpan S := by
  rw [← synth_coeff_of_mem S A hA, unitScalar_conjugation]
  exact action_imaginary_mem S _
    (conjugate_imaginary q (pureScalar (coeff S A)) (pureScalar_re _))

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem action_coe_real (r : ℝ) (v : E) :
    S.action (r : ℍ) v = r • v := by
  simp [S.action_apply]

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem action_normSq (q : ℍ) (v : E) :
    ‖S.action q v‖ ^ 2 = Quaternion.normSq q * ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    action_star_adjoint S]
  change inner ℝ v ((S.action (star q) * S.action q) v) = _
  rw [← map_mul, Quaternion.star_mul_self, action_coe_real]
  simp only [real_inner_smul_right]

omit [FiniteDimensional ℝ E] in
theorem action_injective : Function.Injective S.action := by
  intro q r h
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hzero : S.action (q - r) v = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg (fun A : Module.End ℝ E => A v) h)
  have hs := action_normSq S (q - r) v
  rw [hzero, norm_zero] at hs
  have hvn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  have hq : Quaternion.normSq (q - r) = 0 :=
    (mul_eq_zero.mp (by simpa using hs.symm)).resolve_right hvn
  exact sub_eq_zero.mp (Quaternion.normSq_eq_zero.mp hq)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem unitScalarIsometry_star (q : ℍ) (hq : Quaternion.normSq q = 1) :
    unitScalarIsometry S (star q) (by rw [Quaternion.normSq_star, hq]) =
      (unitScalarIsometry S q hq).symm := by
  ext v
  rfl

theorem unitScalar_mem_normalizer (q : ℍ)
    (hq : Quaternion.normSq q = 1) :
    unitScalarIsometry S q hq ∈
      QuaternionicIsometryNormalizer.normalizer S := by
  intro A
  constructor
  · exact unitScalar_preserves_span S q hq A
  · intro hA
    have hs := unitScalar_preserves_span S (star q)
      (by rw [Quaternion.normSq_star, hq]) _ hA
    rw [unitScalarIsometry_star] at hs
    change QuaternionicIsometryNormalizer.conjugation
      (unitScalarIsometry S q hq)⁻¹
      (QuaternionicIsometryNormalizer.conjugation
        (unitScalarIsometry S q hq) A) ∈ quaternionicSpan S at hs
    rw [← QuaternionicIsometryNormalizer.conjugation_mul] at hs
    simpa using hs

/-- The constructed unit-quaternion action lands in the quaternionic
orthogonal normalizer, providing the actual `Sp(1)` factor. -/
def unitQuaternionNormalizerAction :
    unitary ℍ →* QuaternionicIsometryNormalizer.normalizer S where
  toFun q := ⟨unitQuaternionAction S q,
    unitScalar_mem_normalizer S q (normSq_one_of_unitary q)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (unitQuaternionAction S)
  map_mul' q r := by
    apply Subtype.ext
    exact map_mul (unitQuaternionAction S) q r

private def quaternionI : ℍ := ⟨0, 1, 0, 0⟩
private def quaternionJ : ℍ := ⟨0, 0, 1, 0⟩

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem action_quaternionI (v : E) :
    S.action quaternionI v = S.I v := by
  simp [S.action_apply, quaternionI]

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem action_quaternionJ (v : E) :
    S.action quaternionJ v = S.J v := by
  simp [S.action_apply, quaternionJ]

private theorem central_quaternion_real (q : ℍ)
    (hi : q * quaternionI = quaternionI * q)
    (hj : q * quaternionJ = quaternionJ * q) :
    q = (q.re : ℍ) := by
  have hJ : q.imJ = 0 := by
    have h := congrArg (fun z : ℍ => z.imK) hi
    simp [Quaternion.imK_mul, quaternionI] at h
    linarith
  have hK : q.imK = 0 := by
    have h := congrArg (fun z : ℍ => z.imJ) hi
    simp [Quaternion.imJ_mul, quaternionI] at h
    linarith
  have hI : q.imI = 0 := by
    have h := congrArg (fun z : ℍ => z.imK) hj
    simp [Quaternion.imK_mul, quaternionJ] at h
    linarith
  ext <;> simp [hI, hJ, hK]

/-- A unit scalar whose adjoint rotation is trivial must be one of the two
central signs. -/
theorem unitQuaternion_kernel_sign (q : unitary ℍ)
    (hq : unitQuaternionNormalizerAction S q ∈
      QuaternionicIsometryNormalizer.symplecticKernel S) :
    (q : ℍ) = 1 ∨ (q : ℍ) = -1 := by
  let g := unitQuaternionNormalizerAction S q
  obtain ⟨hI, hJ⟩ :=
    (QuaternionicIsometryNormalizer.mem_symplecticKernel_iff S g).mp hq
  have hqi : (q : ℍ) * quaternionI = quaternionI * q := by
    apply action_injective S
    apply LinearMap.ext
    intro v
    change S.action (q * quaternionI) v =
      S.action (quaternionI * q) v
    rw [map_mul, map_mul]
    change S.action q (S.action quaternionI v) =
      S.action quaternionI (S.action q v)
    rw [action_quaternionI, action_quaternionI]
    exact hI v
  have hqj : (q : ℍ) * quaternionJ = quaternionJ * q := by
    apply action_injective S
    apply LinearMap.ext
    intro v
    change S.action (q * quaternionJ) v =
      S.action (quaternionJ * q) v
    rw [map_mul, map_mul]
    change S.action q (S.action quaternionJ v) =
      S.action quaternionJ (S.action q v)
    rw [action_quaternionJ, action_quaternionJ]
    exact hJ v
  have hreal := central_quaternion_real (q : ℍ) hqi hqj
  have hn : q.1.re ^ 2 = 1 := by
    have hunit := normSq_one_of_unitary q
    rw [hreal, Quaternion.normSq_coe] at hunit
    exact hunit
  rcases sq_eq_one_iff.mp hn with hr | hr
  · left
    simpa [hr] using hreal
  · right
    simpa [hr] using hreal

theorem unitQuaternion_mem_kernel_iff_sign (q : unitary ℍ) :
    unitQuaternionNormalizerAction S q ∈
      QuaternionicIsometryNormalizer.symplecticKernel S ↔
      (q : ℍ) = 1 ∨ (q : ℍ) = -1 := by
  constructor
  · exact unitQuaternion_kernel_sign S q
  · intro hq
    apply (QuaternionicIsometryNormalizer.mem_symplecticKernel_iff S
      (unitQuaternionNormalizerAction S q)).mpr
    constructor
    · intro v
      change S.action (q : ℍ) (S.I v) = S.I (S.action (q : ℍ) v)
      rcases hq with hq | hq <;> rw [hq] <;>
        simp [map_neg]
    · intro v
      change S.action (q : ℍ) (S.J v) = S.J (S.action (q : ℍ) v)
      rcases hq with hq | hq <;> rw [hq] <;>
        simp [map_neg]

theorem symplecticKernel_commutes_unitQuaternion
    (h : QuaternionicIsometryNormalizer.symplecticKernel S)
    (q : unitary ℍ) :
    (h.1 : QuaternionicIsometryNormalizer.normalizer S) *
      unitQuaternionNormalizerAction S q =
      unitQuaternionNormalizerAction S q * h.1 := by
  obtain ⟨hI, hJ⟩ :=
    (QuaternionicIsometryNormalizer.mem_symplecticKernel_iff S h.1).mp h.2
  apply Subtype.ext
  ext v
  change (h.1.1) (S.action (q : ℍ) v) =
    S.action (q : ℍ) (h.1.1 v)
  exact S.action_commutes h.1.1.toLinearEquiv.toLinearMap hI hJ (q : ℍ) v

/-- The usual compact product action, constructed from the genuine
quaternion-linear kernel and scalar unit-quaternion action. -/
def symplecticProductAction :
    (QuaternionicIsometryNormalizer.symplecticKernel S × unitary ℍ) →*
      QuaternionicIsometryNormalizer.normalizer S where
  toFun p := p.1.1 * unitQuaternionNormalizerAction S p.2
  map_one' := by simp
  map_mul' p r := by
    change (p.1.1 * r.1.1) * unitQuaternionNormalizerAction S (p.2 * r.2) =
      (p.1.1 * unitQuaternionNormalizerAction S p.2) *
      (r.1.1 * unitQuaternionNormalizerAction S r.2)
    rw [map_mul]
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    rw [mul_assoc, symplecticKernel_commutes_unitQuaternion S r.1 p.2]
    simp only [mul_assoc]

theorem symplecticProduct_kernel_sign
    (p : QuaternionicIsometryNormalizer.symplecticKernel S × unitary ℍ)
    (hp : symplecticProductAction S p = 1) :
    (p.2 : ℍ) = 1 ∨ (p.2 : ℍ) = -1 := by
  have heq : unitQuaternionNormalizerAction S p.2 =
      (p.1.1 : QuaternionicIsometryNormalizer.normalizer S)⁻¹ := by
    calc
      unitQuaternionNormalizerAction S p.2 =
          (p.1.1 : QuaternionicIsometryNormalizer.normalizer S)⁻¹ *
            ((p.1.1 : QuaternionicIsometryNormalizer.normalizer S) *
              unitQuaternionNormalizerAction S p.2) := by simp
      _ = (p.1.1 : QuaternionicIsometryNormalizer.normalizer S)⁻¹ := by
        simpa only [symplecticProductAction, mul_one] using
          congrArg (fun z : QuaternionicIsometryNormalizer.normalizer S =>
            (p.1.1 : QuaternionicIsometryNormalizer.normalizer S)⁻¹ * z) hp
  apply (unitQuaternion_mem_kernel_iff_sign S p.2).mp
  rw [heq]
  exact (QuaternionicIsometryNormalizer.symplecticKernel S).inv_mem p.1.2

end
end QuaternionicSymmetry.QuaternionicUnitScalarIsometries
