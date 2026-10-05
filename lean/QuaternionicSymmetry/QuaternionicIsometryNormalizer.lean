import QuaternionicSymmetry.ManifoldQuaternionicUnitaryNormalizer

/-! The orthogonal normalizer of a quaternionic three-plane in a real inner
product space. This is the fixed-model structure group of adapted frames. -/

namespace QuaternionicSymmetry.QuaternionicIsometryNormalizer

open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicRankThreeOrthogonal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Conjugation of continuous endomorphisms by an orthogonal isomorphism. -/
def conjugation (g : E ≃ₗᵢ[ℝ] E) :
    (E →L[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E) :=
  (g.toContinuousLinearEquiv.conjContinuousAlgEquiv).toLinearEquiv

@[simp] theorem conjugation_apply (g : E ≃ₗᵢ[ℝ] E)
    (A : E →L[ℝ] E) (v : E) :
    conjugation g A v = g (A (g.symm v)) := rfl

@[simp] theorem conjugation_one (A : E →L[ℝ] E) :
    conjugation (1 : E ≃ₗᵢ[ℝ] E) A = A := by
  ext v
  change A v = A v
  rfl

@[simp] theorem conjugation_mul (g h : E ≃ₗᵢ[ℝ] E)
    (A : E →L[ℝ] E) :
    conjugation (g * h) A = conjugation g (conjugation h A) := by
  ext v
  simp [LinearIsometryEquiv.mul_def]

@[simp] theorem conjugation_inv (g : E ≃ₗᵢ[ℝ] E)
    (A : E →L[ℝ] E) :
    conjugation g⁻¹ A = (conjugation g).symm A := by
  apply (conjugation g).injective
  rw [← conjugation_mul]
  simp

/-- The normalizer consists of exactly the isometries whose adjoint action
preserves the quaternionic three-plane. -/
def normalizer (S : QuaternionicStructure E) : Subgroup (E ≃ₗᵢ[ℝ] E) where
  carrier := {g | ∀ A : E →L[ℝ] E,
    A ∈ quaternionicSpan S ↔ conjugation g A ∈ quaternionicSpan S}
  one_mem' := by
    intro A
    simp
  mul_mem' := by
    intro g h hg hh A
    rw [conjugation_mul, ← hg, ← hh]
  inv_mem' := by
    intro g hg A
    constructor
    · intro hA
      have := (hg (conjugation g⁻¹ A)).mpr (by
        simpa [← conjugation_mul] using hA)
      exact this
    · intro hA
      have := (hg (conjugation g⁻¹ A)).mp hA
      simpa [← conjugation_mul] using this

variable [Nontrivial E] [FiniteDimensional ℝ E]

/-- The three-dimensional adjoint action of a quaternionic normalizer. -/
def rotationLinear (S : QuaternionicStructure E)
    (g : normalizer S) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (coeff S).toLinearMap.comp
    ((conjugation g.1).toLinearMap.comp (synth S).toLinearMap)

theorem rotationLinear_apply (S : QuaternionicStructure E)
    (g : normalizer S) (a : Fin 3 → ℝ) :
    rotationLinear S g a = coeff S (conjugation g.1 (synth S a)) := rfl

/-- The adjoint action really closes on the quaternionic three-plane. -/
theorem synth_rotationLinear (S : QuaternionicStructure E)
    (g : normalizer S) (a : Fin 3 → ℝ) :
    synth S (rotationLinear S g a) = conjugation g.1 (synth S a) := by
  rw [rotationLinear_apply]
  apply synth_coeff_of_mem
  exact (g.2 (synth S a)).mp (synth_mem S a)

theorem rotationLinear_inv (S : QuaternionicStructure E)
    (g : normalizer S) (a : Fin 3 → ℝ) :
    rotationLinear S (g⁻¹) (rotationLinear S g a) = a := by
  apply (show Function.Injective (synth S) from
    Function.LeftInverse.injective (coeff_synth S))
  rw [synth_rotationLinear, synth_rotationLinear, ← conjugation_mul]
  simp

theorem rotationLinear_mul (S : QuaternionicStructure E)
    (g h : normalizer S) (a : Fin 3 → ℝ) :
    rotationLinear S (g * h) a = rotationLinear S g (rotationLinear S h a) := by
  apply (show Function.Injective (synth S) from
    Function.LeftInverse.injective (coeff_synth S))
  rw [synth_rotationLinear, synth_rotationLinear, synth_rotationLinear,
    Subgroup.coe_mul, conjugation_mul]

/-- The normalizer acts invertibly on its quaternionic three-plane. -/
def rotationEquiv (S : QuaternionicStructure E)
    (g : normalizer S) : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toLinearMap := rotationLinear S g
  invFun := rotationLinear S (g⁻¹)
  left_inv := rotationLinear_inv S g
  right_inv a := by
    simpa using rotationLinear_inv S (g⁻¹) a

@[simp] theorem rotationEquiv_apply (S : QuaternionicStructure E)
    (g : normalizer S) (a : Fin 3 → ℝ) :
    rotationEquiv S g a = rotationLinear S g a := rfl

/-- The kernel consists exactly of isometries commuting with the three
quaternionic generators, the intrinsic `Sp(n)` subgroup of this model. -/
theorem rotation_kernel_iff_commutes (S : QuaternionicStructure E)
    (g : normalizer S) :
    rotationEquiv S g = LinearEquiv.refl ℝ (Fin 3 → ℝ) ↔
      (∀ v : E, g.1 (S.I v) = S.I (g.1 v)) ∧
      (∀ v : E, g.1 (S.J v) = S.J (g.1 v)) := by
  constructor
  · intro h
    have hgen (t : Fin 3) (v : E) :
        g.1 (quaternionicGenerator S t v) =
          quaternionicGenerator S t (g.1 v) := by
      have hs := synth_rotationLinear S g (Pi.basisFun ℝ (Fin 3) t)
      rw [← rotationEquiv_apply, h, LinearEquiv.refl_apply,
        synth_basis] at hs
      have he := congrArg (fun A : E →L[ℝ] E => A (g.1 v)) hs
      simpa only [conjugation_apply, g.1.symm_apply_apply] using he.symm
    constructor
    · intro v
      exact hgen 0 v
    · intro v
      exact hgen 1 v
  · rintro ⟨hI, hJ⟩
    have hK : ∀ v : E, g.1 (S.K v) = S.K (g.1 v) := by
      intro v
      change g.1 (S.I (S.J v)) = S.I (S.J (g.1 v))
      rw [hI, hJ]
    apply LinearEquiv.ext
    intro a
    apply (show Function.Injective (synth S) from
      Function.LeftInverse.injective (coeff_synth S))
    rw [rotationEquiv_apply, synth_rotationLinear]
    ext v
    change g.1 (synth S a (g.1.symm v)) = synth S a v
    rw [synth_apply]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    fin_cases t
    · simpa only [quaternionicGenerator, g.1.apply_symm_apply] using
        hI (g.1.symm v)
    · simpa only [quaternionicGenerator, g.1.apply_symm_apply] using
        hJ (g.1.symm v)
    · simpa only [quaternionicGenerator, g.1.apply_symm_apply] using
        hK (g.1.symm v)

/-- The adjoint representation of the orthogonal quaternionic normalizer. -/
def rotationHom (S : QuaternionicStructure E) :
    normalizer S →* ((Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) where
  toFun := rotationEquiv S
  map_one' := by
    apply LinearEquiv.ext
    intro a
    apply (show Function.Injective (synth S) from
      Function.LeftInverse.injective (coeff_synth S))
    rw [rotationEquiv_apply, synth_rotationLinear]
    change conjugation (1 : E ≃ₗᵢ[ℝ] E) (synth S a) = synth S a
    simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro a
    exact rotationLinear_mul S g h a

/-- Intrinsic compact symplectic subgroup: the kernel of the quaternionic
normalizer's three-dimensional adjoint representation. -/
def symplecticKernel (S : QuaternionicStructure E) : Subgroup (normalizer S) :=
  (rotationHom S).ker

theorem mem_symplecticKernel_iff (S : QuaternionicStructure E)
    (g : normalizer S) :
    g ∈ symplecticKernel S ↔
      (∀ v : E, g.1 (S.I v) = S.I (g.1 v)) ∧
      (∀ v : E, g.1 (S.J v) = S.J (g.1 v)) := by
  change rotationHom S g = 1 ↔ _
  exact rotation_kernel_iff_commutes S g

end
end QuaternionicSymmetry.QuaternionicIsometryNormalizer
