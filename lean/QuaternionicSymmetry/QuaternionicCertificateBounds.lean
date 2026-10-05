import QuaternionicSymmetry.QuaternionicCertificateGenerators
import QuaternionicSymmetry.CertificateFamily

/-! The complete finite certificate inequalities for actual pointwise
quaternionic exterior forms in dimensions two through ten. -/

namespace QuaternionicSymmetry.QuaternionicCertificateBounds

open Module QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicCertificateGenerators AlgebraCertificates

noncomputable section

variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem functional_lower_bound (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : 2 ≤ Q.quaternionicDimension) (hn' : Q.quaternionicDimension ≤ 10)
    (hr : Fintype.card κ = 2 * Q.quaternionicDimension + 2)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    (scalarCoefficient Q.quaternionicDimension : ℝ) *
      L (embed (V := V) (form Q c) ^ Q.quaternionicDimension) ≤
    L (evaluateForms Q c B η (CertificateFamily.polynomial Q.quaternionicDimension)) := by
  let J : P →ₗ[ℚ] ℝ :=
    (L.restrictScalars ℚ).comp (evaluateForms Q c B η).toLinearMap
  have hc : 3 ≤ Fintype.card κ := by omega
  have h := CertificateFamily.functional_lower_bound J Q.quaternionicDimension hn hn'
    (fun k hk => PositiveRay.functional_nonneg
      (Z₁_power_mixed_positive Q c B hB η hη k hk) L hL)
    (fun hk => PositiveRay.functional_nonneg (F₂_mixed_positive Q c B hB η hη hk) L hL)
    (fun hk => PositiveRay.functional_nonneg (F₃_mixed_positive Q c B hB η hη hk) L hL)
    (fun hk => PositiveRay.functional_nonneg (F₄_mixed_positive Q c B hB η hη hk) L hL)
    (fun hk => ?_) (fun hk => ?_) (fun hk => ?_)
  · change (scalarCoefficient Q.quaternionicDimension : ℝ) *
      L (evaluateForms Q c B η (U ^ Q.quaternionicDimension)) ≤ _ at h
    simpa only [map_pow, evaluateForms_U] using h
  · simpa only [hr, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      PositiveRay.functional_nonneg (M₂₁_mixed_positive Q c B hB η hη hk) L hL
  · simpa only [hr, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      PositiveRay.functional_nonneg (M₃₁_mixed_positive Q c B hB η hη hk) L hL
  · simpa only [hr, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      PositiveRay.functional_nonneg (M₃₂_mixed_positive Q c hc B hB η hη hk) L hL

theorem remainder_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : 2 ≤ Q.quaternionicDimension) (hn' : Q.quaternionicDimension ≤ 10)
    (hr : Fintype.card κ = 2 * Q.quaternionicDimension + 2)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (evaluateForms Q c B η (CertificateFamily.polynomial Q.quaternionicDimension) -
        (scalarCoefficient Q.quaternionicDimension : ℝ) •
          embed (V := V) (form Q c) ^ Q.quaternionicDimension) := by
  apply (PositiveRay.contains_iff_functional_nonneg (embed_topForm_ne_zero Q c)).mpr
  intro L hL
  rw [map_sub, map_smul, smul_eq_mul]
  exact sub_nonneg.mpr (functional_lower_bound Q c hn hn' hr B hB η hη L hL)

omit [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] [FiniteDimensional ℝ V] in
theorem fundamental_functional_pos (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 < L (embed (V := V) (topForm Q c))) :
    0 < L (embed (V := V) (form Q c) ^ Q.quaternionicDimension) := by
  rw [← map_pow, fundamental_pow_eq]
  have he := (embed (V := V)).toLinearMap.map_smul
    ((2 * Q.quaternionicDimension + 1).factorial : ℝ) (topForm Q c)
  change embed (V := V) (((2 * Q.quaternionicDimension + 1).factorial : ℝ) • topForm Q c) =
    ((2 * Q.quaternionicDimension + 1).factorial : ℝ) • embed (V := V) (topForm Q c) at he
  rw [he, L.map_smul, smul_eq_mul]
  exact mul_pos (by positivity) hL

theorem functional_strict_positive (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : 2 ≤ Q.quaternionicDimension) (hn' : Q.quaternionicDimension ≤ 10)
    (hr : Fintype.card κ = 2 * Q.quaternionicDimension + 2)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 < L (embed (V := V) (topForm Q c))) :
    0 < L (evaluateForms Q c B η (CertificateFamily.polynomial Q.quaternionicDimension)) := by
  apply lt_of_lt_of_le _ (functional_lower_bound Q c hn hn' hr B hB η hη L hL.le)
  apply mul_pos _ (fundamental_functional_pos Q c L hL)
  exact_mod_cast scalarCoefficient_pos (by omega : 0 < Q.quaternionicDimension)

end
end QuaternionicSymmetry.QuaternionicCertificateBounds
