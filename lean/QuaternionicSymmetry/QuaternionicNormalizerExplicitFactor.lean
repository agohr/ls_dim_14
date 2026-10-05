import QuaternionicSymmetry.QuaternionicNormalizerProductSurjective

/-! A specified unit quaternion matching the two normalizer axes gives a
specific symplectic factor. This lets local smooth quaternion formulas factor
actual transitions without a pointwise `Classical.choose`. -/

namespace QuaternionicSymmetry.QuaternionicNormalizerExplicitFactor

open scoped Quaternion
open QuaternionicIsometryNormalizer QuaternionicUnitScalarIsometries
  QuaternionicUnitQuaternionTransport QuaternionicNormalizerRotationAxes

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
variable (S : QuaternionicStructure E)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem action_basisI (v : E) : S.action basisI v = S.I v := by
  simp [S.action_apply, basisI]

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem action_basisJ (v : E) : S.action basisJ v = S.J v := by
  simp [S.action_apply, basisJ]

/-- A fixed scalar factor carrying the standard axes to those of `g`
determines a quaternion-linear isometry factor of `g`. -/
theorem factor_of_axis_lift (g : normalizer S) (q : unitary ℍ)
    (hqi : (q : ℍ) * basisI = firstAxis S g * q)
    (hqj : (q : ℍ) * basisJ = secondAxis S g * q) :
    ∃ h : symplecticKernel S,
      symplecticProductAction S (h, q) = g := by
  let T := unitQuaternionNormalizerAction S q
  have hTi (v : E) : T.1 (S.I v) =
      S.action (firstAxis S g) (T.1 v) := by
    change S.action (q : ℍ) (S.I v) =
      S.action (firstAxis S g) (S.action (q : ℍ) v)
    rw [← action_basisI S v]
    change (S.action (q : ℍ) * S.action basisI) v =
      (S.action (firstAxis S g) * S.action (q : ℍ)) v
    rw [← map_mul, ← map_mul]
    rw [hqi]
  have hTj (v : E) : T.1 (S.J v) =
      S.action (secondAxis S g) (T.1 v) := by
    change S.action (q : ℍ) (S.J v) =
      S.action (secondAxis S g) (S.action (q : ℍ) v)
    rw [← action_basisJ S v]
    change (S.action (q : ℍ) * S.action basisJ) v =
      (S.action (secondAxis S g) * S.action (q : ℍ)) v
    rw [← map_mul, ← map_mul]
    rw [hqj]
  let h : normalizer S := T⁻¹ * g
  have hcommI (v : E) : h.1 (S.I v) = S.I (h.1 v) := by
    apply T.1.injective
    have hg := (firstAxis_action S g v).symm
    change g.1 (S.I v) = S.action (firstAxis S g) (g.1 v) at hg
    change T.1 (h.1 (S.I v)) = T.1 (S.I (h.1 v))
    rw [hTi]
    change T.1 (T.1.symm (g.1 (S.I v))) =
      S.action (firstAxis S g)
        (T.1 (T.1.symm (g.1 v)))
    rw [T.1.apply_symm_apply, T.1.apply_symm_apply]
    exact hg
  have hcommJ (v : E) : h.1 (S.J v) = S.J (h.1 v) := by
    apply T.1.injective
    have hg := (secondAxis_action S g v).symm
    change g.1 (S.J v) = S.action (secondAxis S g) (g.1 v) at hg
    change T.1 (h.1 (S.J v)) = T.1 (S.J (h.1 v))
    rw [hTj]
    change T.1 (T.1.symm (g.1 (S.J v))) =
      S.action (secondAxis S g)
        (T.1 (T.1.symm (g.1 v)))
    rw [T.1.apply_symm_apply, T.1.apply_symm_apply]
    exact hg
  have hh : h ∈ symplecticKernel S :=
    (mem_symplecticKernel_iff S h).mpr ⟨hcommI, hcommJ⟩
  refine ⟨⟨h, hh⟩, ?_⟩
  change h * T = g
  have hcentral := symplecticKernel_commutes_unitQuaternion S
    (⟨h, hh⟩ : symplecticKernel S) q
  change h * T = T * h at hcentral
  rw [hcentral]
  dsimp [h]
  group

end
end QuaternionicSymmetry.QuaternionicNormalizerExplicitFactor
