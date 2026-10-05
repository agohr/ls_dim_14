import QuaternionicSymmetry.QuaternionicNormalizerRotationAxes

/-! Constructive pointwise factorization of the quaternionic orthogonal
normalizer as `Sp(n) · Sp(1)`. -/

namespace QuaternionicSymmetry.QuaternionicNormalizerProductSurjective

open scoped Quaternion
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
  QuaternionicIsometryNormalizer QuaternionicUnitScalarIsometries
  QuaternionicUnitQuaternionTransport QuaternionicUnitQuaternionPairTransport
  QuaternionicNormalizerRotationAxes

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
variable (S : QuaternionicStructure E)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem action_basisI (v : E) :
    S.action basisI v = S.I v := by
  simp [S.action_apply, basisI]

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem action_basisJ (v : E) :
    S.action basisJ v = S.J v := by
  simp [S.action_apply, basisJ]

private theorem scalar_conjugation_first (q : unitary ℍ) (u : ℍ)
    (hq : (q : ℍ) * basisI = u * q) :
    conjugation (unitQuaternionNormalizerAction S q).1
      (quaternionicGenerator S 0) =
      Module.End.toContinuousLinearMap E (S.action u) := by
  ext z
  let T := (unitQuaternionNormalizerAction S q).1
  let v := T.symm z
  have hv : T v = z := T.apply_symm_apply z
  change S.action (q : ℍ) (S.I v) = S.action u z
  rw [← action_basisI S v, ← hv]
  have h := congrArg (fun p : ℍ => S.action p v) hq
  change S.action ((q : ℍ) * basisI) v = S.action (u * q) v at h
  rw [map_mul, map_mul] at h
  exact h

private theorem scalar_conjugation_second (q : unitary ℍ) (v : ℍ)
    (hq : (q : ℍ) * basisJ = v * q) :
    conjugation (unitQuaternionNormalizerAction S q).1
      (quaternionicGenerator S 1) =
      Module.End.toContinuousLinearMap E (S.action v) := by
  ext z
  let T := (unitQuaternionNormalizerAction S q).1
  let w := T.symm z
  have hw : T w = z := T.apply_symm_apply z
  change S.action (q : ℍ) (S.J w) = S.action v z
  rw [← action_basisJ S w, ← hw]
  have h := congrArg (fun p : ℍ => S.action p w) hq
  change S.action ((q : ℍ) * basisJ) w = S.action (v * q) w at h
  rw [map_mul, map_mul] at h
  exact h

private theorem normalizer_conjugation_first (g : normalizer S) :
    conjugation g.1 (quaternionicGenerator S 0) =
      Module.End.toContinuousLinearMap E (S.action (firstAxis S g)) := by
  ext z
  let w := g.1.symm z
  have hw : g.1 w = z := g.1.apply_symm_apply z
  change g.1 (S.I w) = S.action (firstAxis S g) z
  rw [← hw]
  exact (firstAxis_action S g w).symm

private theorem normalizer_conjugation_second (g : normalizer S) :
    conjugation g.1 (quaternionicGenerator S 1) =
      Module.End.toContinuousLinearMap E (S.action (secondAxis S g)) := by
  ext z
  let w := g.1.symm z
  have hw : g.1 w = z := g.1.apply_symm_apply z
  change g.1 (S.J w) = S.action (secondAxis S g) z
  rw [← hw]
  exact (secondAxis_action S g w).symm

/-- Every orthogonal quaternionic normalizer element is the product of a
quaternion-linear isometry and a genuine unit-quaternion scalar action. -/
theorem symplecticProductAction_surjective :
    Function.Surjective (symplecticProductAction S) := by
  intro g
  obtain ⟨q, hqi, hqj⟩ := exists_unitPairTransport
    (firstAxis S g) (secondAxis S g)
    (firstAxis_re S g) (secondAxis_re S g)
    (firstAxis_normSq S g) (secondAxis_normSq S g)
    (axes_anticommute S g)
  let T := unitQuaternionNormalizerAction S q
  have hfirst : conjugation g.1 (quaternionicGenerator S 0) =
      conjugation T.1 (quaternionicGenerator S 0) := by
    rw [normalizer_conjugation_first S g,
      scalar_conjugation_first S q (firstAxis S g) hqi]
  have hsecond : conjugation g.1 (quaternionicGenerator S 1) =
      conjugation T.1 (quaternionicGenerator S 1) := by
    rw [normalizer_conjugation_second S g,
      scalar_conjugation_second S q (secondAxis S g) hqj]
  let h : normalizer S := T⁻¹ * g
  have hconj (A : E →L[ℝ] E)
      (hA : conjugation g.1 A = conjugation T.1 A) :
      conjugation h.1 A = A := by
    change conjugation (T.1⁻¹ * g.1) A = A
    rw [conjugation_mul, hA, ← conjugation_mul]
    simp
  have hmem : h ∈ symplecticKernel S := by
    apply (mem_symplecticKernel_iff S h).mpr
    constructor
    · intro v
      have he := congrArg (fun A : E →L[ℝ] E => A (h.1 v))
        (hconj _ hfirst)
      simpa only [conjugation_apply, h.1.symm_apply_apply] using he
    · intro v
      have he := congrArg (fun A : E →L[ℝ] E => A (h.1 v))
        (hconj _ hsecond)
      simpa only [conjugation_apply, h.1.symm_apply_apply] using he
  refine ⟨(⟨h, hmem⟩, q), ?_⟩
  change h * T = g
  have hcomm := symplecticKernel_commutes_unitQuaternion S
    (⟨h, hmem⟩ : symplecticKernel S) q
  change h * T = T * h at hcomm
  rw [hcomm]
  dsimp [h]
  group

end
end QuaternionicSymmetry.QuaternionicNormalizerProductSurjective
