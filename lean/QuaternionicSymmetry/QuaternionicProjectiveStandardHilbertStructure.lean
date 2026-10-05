import QuaternionicSymmetry.QuaternionicProjectiveStandardL2

/-! The fixed left-quaternionic Hermitian structure on the Hilbert direct
sum used by the projective standard representation. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveStandardHilbertStructure

open scoped Quaternion
open QuaternionicProjectiveStandardL2
open QuaternionicUnitQuaternionTransport
open QuaternionicUnitScalarIsometries

noncomputable section

def leftUnitIsometry (q : unitary ℍ) : ℍ ≃ₗᵢ[ℝ] ℍ where
  toFun w := (q : ℍ) * w
  invFun w := star (q : ℍ) * w
  map_add' a b := mul_add _ a b
  map_smul' r w := by
    simp only [Algebra.smul_def]
    simpa only [← mul_assoc] using
      congrArg (fun z : ℍ => z * w) (Algebra.commutes r (q : ℍ)).symm
  left_inv w := by
    have hs : star (q : ℍ) * (q : ℍ) = 1 :=
      (Unitary.mem_iff.mp q.property).1
    change star (q : ℍ) * ((q : ℍ) * w) = w
    rw [← mul_assoc, hs, one_mul]
  right_inv w := by
    have hs : (q : ℍ) * star (q : ℍ) = 1 :=
      (Unitary.mem_iff.mp q.property).2
    change (q : ℍ) * (star (q : ℍ) * w) = w
    rw [← mul_assoc, hs, one_mul]
  norm_map' w := by
    have hq : ‖(q : ℍ)‖ = 1 := by
      have hs := Quaternion.normSq_eq_norm_mul_self (q : ℍ)
      rw [normSq_one_of_unitary] at hs
      nlinarith [norm_nonneg (q : ℍ)]
    change ‖(q : ℍ) * w‖ = ‖w‖
    rw [norm_mul, hq, one_mul]

@[simp] theorem leftUnitIsometry_apply (q : unitary ℍ) (w : ℍ) :
    leftUnitIsometry q w = (q : ℍ) * w := rfl

def leftLineI : ℍ ≃ₗᵢ[ℝ] ℍ :=
  leftUnitIsometry (ofNormSqOne basisI basisI_unit.2)

def leftLineJ : ℍ ≃ₗᵢ[ℝ] ℍ :=
  leftUnitIsometry (ofNormSqOne basisJ basisJ_unit.2)

@[simp] theorem leftLineI_apply (w : ℍ) : leftLineI w = basisI * w := rfl
@[simp] theorem leftLineJ_apply (w : ℍ) : leftLineJ w = basisJ * w := rfl

def leftLineStructure : QuaternionicStructure ℍ where
  I := leftLineI
  J := leftLineJ
  I_sq w := by
    change basisI * (basisI * w) = -w
    rw [← mul_assoc, imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2]
    simp
  J_sq w := by
    change basisJ * (basisJ * w) = -w
    rw [← mul_assoc, imaginaryUnit_sq basisJ basisJ_unit.1 basisJ_unit.2]
    simp
  I_J_anti w := by
    change basisI * (basisJ * w) = -(basisJ * (basisI * w))
    have h : basisI * basisJ = -basisJ * basisI := by
      ext <;> norm_num [basisI, basisJ, Quaternion.re_mul,
        Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
    rw [← mul_assoc, h]
    simp [mul_assoc]

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def prodL2Isometry (e : E ≃ₗᵢ[ℝ] E) (f : F ≃ₗᵢ[ℝ] F) :
    WithLp 2 (E × F) ≃ₗᵢ[ℝ] WithLp 2 (E × F) :=
  LinearIsometryEquiv.mk
    (((WithLp.linearEquiv 2 ℝ (E × F)).trans
      (e.toLinearEquiv.prodCongr f.toLinearEquiv)).trans
      (WithLp.linearEquiv 2 ℝ (E × F)).symm)
    (by
      intro z
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [WithLp.prod_norm_sq_eq_of_L2,
        WithLp.prod_norm_sq_eq_of_L2]
      simp [e.norm_map, f.norm_map])

@[simp] theorem prodL2Isometry_fst
    (e : E ≃ₗᵢ[ℝ] E) (f : F ≃ₗᵢ[ℝ] F)
    (z : WithLp 2 (E × F)) :
    (prodL2Isometry e f z).fst = e z.fst := rfl

@[simp] theorem prodL2Isometry_snd
    (e : E ≃ₗᵢ[ℝ] E) (f : F ≃ₗᵢ[ℝ] F)
    (z : WithLp 2 (E × F)) :
    (prodL2Isometry e f z).snd = f z.snd := rfl

variable [Nontrivial E] [FiniteDimensional ℝ E]

def standardStructure (S : QuaternionicStructure E) :
    QuaternionicStructure (StandardSpace (E := E)) where
  I := prodL2Isometry S.I leftLineStructure.I
  J := prodL2Isometry S.J leftLineStructure.J
  I_sq z := by
    apply (WithLp.linearEquiv 2 ℝ (E × ℍ)).injective
    apply Prod.ext
    · simp [S.I_sq]
    · simp [leftLineStructure.I_sq]
  J_sq z := by
    apply (WithLp.linearEquiv 2 ℝ (E × ℍ)).injective
    apply Prod.ext
    · simp [S.J_sq]
    · simp [leftLineStructure.J_sq]
  I_J_anti z := by
    apply (WithLp.linearEquiv 2 ℝ (E × ℍ)).injective
    apply Prod.ext
    · simp [S.I_J_anti]
    · simp [leftLineStructure.I_J_anti]

theorem standardIsometryL2_commutes_I (S : QuaternionicStructure E)
    (p : QuaternionicIsometryNormalizer.symplecticKernel S × unitary ℍ)
    (z : StandardSpace (E := E)) :
    standardIsometryL2 S p ((standardStructure S).I z) =
      (standardStructure S).I (standardIsometryL2 S p z) := by
  have hp := (QuaternionicIsometryNormalizer.mem_symplecticKernel_iff S p.1.1).mp p.1.2
  apply (WithLp.linearEquiv 2 ℝ (E × ℍ)).injective
  apply Prod.ext
  · change p.1.1.1 (S.I z.fst) = S.I (p.1.1.1 z.fst)
    exact hp.1 z.fst
  · change (basisI * z.snd) * star (p.2 : ℍ) =
      basisI * (z.snd * star (p.2 : ℍ))
    rw [mul_assoc]

theorem standardIsometryL2_commutes_J (S : QuaternionicStructure E)
    (p : QuaternionicIsometryNormalizer.symplecticKernel S × unitary ℍ)
    (z : StandardSpace (E := E)) :
    standardIsometryL2 S p ((standardStructure S).J z) =
      (standardStructure S).J (standardIsometryL2 S p z) := by
  have hp := (QuaternionicIsometryNormalizer.mem_symplecticKernel_iff S p.1.1).mp p.1.2
  apply (WithLp.linearEquiv 2 ℝ (E × ℍ)).injective
  apply Prod.ext
  · change p.1.1.1 (S.J z.fst) = S.J (p.1.1.1 z.fst)
    exact hp.2 z.fst
  · change (basisJ * z.snd) * star (p.2 : ℍ) =
      basisJ * (z.snd * star (p.2 : ℍ))
    rw [mul_assoc]

/-- Intrinsic quaternion-linear isometry group of a real quaternionic
Hilbert space, the compact symplectic group in this model. -/
def quaternionicUnitaryGroup {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : QuaternionicStructure V) : Subgroup (V ≃ₗᵢ[ℝ] V) where
  carrier := {g | (∀ v, g (T.I v) = T.I (g v)) ∧
    (∀ v, g (T.J v) = T.J (g v))}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    constructor <;> intro v
    · simpa [LinearIsometryEquiv.mul_def] using
        congrArg g (hh.1 v) |>.trans (hg.1 (h v))
    · simpa [LinearIsometryEquiv.mul_def] using
        congrArg g (hh.2 v) |>.trans (hg.2 (h v))
  inv_mem' := by
    intro g hg
    constructor <;> intro v
    · apply g.injective
      simpa using (hg.1 (g.symm v)).symm
    · apply g.injective
      simpa using (hg.2 (g.symm v)).symm

/-- The standard block action lands in the genuine quaternionic unitary
group of the Hilbert direct sum. -/
def standardSymplecticAction (S : QuaternionicStructure E) :
    (QuaternionicIsometryNormalizer.symplecticKernel S × unitary ℍ) →*
      quaternionicUnitaryGroup (standardStructure S) where
  toFun p := ⟨standardIsometryL2 S p,
    ⟨standardIsometryL2_commutes_I S p,
      standardIsometryL2_commutes_J S p⟩⟩
  map_one' := Subtype.ext (map_one (standardIsometryL2 S))
  map_mul' p r := Subtype.ext (map_mul (standardIsometryL2 S) p r)

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardHilbertStructure
