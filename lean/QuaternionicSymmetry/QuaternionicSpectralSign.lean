import QuaternionicSymmetry.QuaternionicEigenbasisTransport
import QuaternionicSymmetry.QuaternionicEigenbasisFinite
import QuaternionicSymmetry.QuaternionicBlockVolume
import QuaternionicSymmetry.PositiveRay

/-! The intrinsic quaternionic spectral formula and its sign, for actual
exterior two-forms on every finite-dimensional quaternionic Hermitian space. -/

namespace QuaternionicSymmetry.QuaternionicSpectralSign

open Module
open QuaternionicEigenbasisTransport QuaternionicSpectralCoefficients
open QuaternionicFundamental HyperholomorphicExterior

noncomputable section

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The spectral parameters give the exact coefficient of the canonical top form. -/
theorem exists_spectral_formula (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer) :
    ∃ vals : Fin Q.quaternionicDimension → ℝ, ∀ k ≤ Q.quaternionicDimension,
      (-(evenForm c A) ^ 2) ^ k * QuaternionicFundamental.form Q c ^
          (Q.quaternionicDimension - k) =
        (((2 * k).factorial : ℝ) *
          ((2 * (Q.quaternionicDimension - k) + 1).factorial : ℝ) *
          spectralWeight vals k) • topForm Q c := by
  classical
  obtain ⟨vals, v, b, hb, heig⟩ := Q.exists_eigenOrthonormalBasis_fin A hA
  refine ⟨vals, fun k hk => ?_⟩
  have h := signed_mixed_eq_map (transport b.toBasis) vals k (by simpa using hk)
  rw [transport_theta Q A hA vals v b hb heig,
    transport_fundamental Q v b hb, transport_volume Q v b hb] at h
  simpa only [Fintype.card_fin, evenForm_basis_independent b.toBasis c,
    QuaternionicFundamental.form_basis_independent Q b.toBasis c,
    topForm_basis_independent Q b.toBasis c] using h

/-- The canonical quaternionic top form is nonzero. -/
theorem topForm_ne_zero (Q : QuaternionicStructure V) (c : Basis ι ℝ V) :
    topForm Q c ≠ 0 := by
  classical
  obtain ⟨vals, v, b, hb, heig⟩ :=
    Q.exists_eigenOrthonormalBasis_fin 0 Q.skewCentralizer.zero_mem
  rw [← topForm_basis_independent Q b.toBasis c, ← transport_volume Q v b hb]
  intro h
  apply QuaternionicBlockVolume.volume_fin_ne_zero Q.quaternionicDimension
  have hz : (QuaternionicPencilPolynomial.volume :
      QuaternionicPencilPolynomial.Eev (Fin Q.quaternionicDimension)) = 0 :=
    transport_injective b.toBasis (by simpa only [map_zero] using h)
  exact congrArg Subtype.val hz

/-- Normalization at the canonical top form is possible, so its positive ray is nonvacuous. -/
theorem exists_normalizedFunctional (Q : QuaternionicStructure V) (c : Basis ι ℝ V) :
    ∃ L : E V →ₗ[ℝ] ℝ, L (topForm Q c) = 1 := by
  letI : Module.Projective ℝ (E V) :=
    Module.Projective.of_basis (Basis.ofVectorSpace ℝ (E V))
  exact Module.Projective.exists_dual_eq_one ℝ (V := E V) (topForm_ne_zero Q c)

/-- Positivity with respect to the intrinsic quaternionic orientation. -/
theorem signed_mixed_nonneg (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension)
    (L : E V →ₗ[ℝ] ℝ) (hvol : 0 ≤ L (topForm Q c)) :
    0 ≤ L ((-(evenForm c A) ^ 2) ^ k * QuaternionicFundamental.form Q c ^
      (Q.quaternionicDimension - k)) := by
  obtain ⟨vals, hvals⟩ := exists_spectral_formula Q c A hA
  rw [hvals k hk, map_smul, smul_eq_mul]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (spectralWeight_nonneg vals k)) hvol

/-- The signed mixed form belongs to the nonnegative ray of the canonical orientation. -/
theorem signed_mixed_mem_positiveRay (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c)
      ((-(evenForm c A) ^ 2) ^ k * QuaternionicFundamental.form Q c ^
        (Q.quaternionicDimension - k)) := by
  apply (PositiveRay.contains_iff_functional_nonneg (topForm_ne_zero Q c)).mpr
  exact fun L hL => signed_mixed_nonneg Q c A hA k hk L hL

/-- The sign can equivalently be normalized by the top power of the fundamental form. -/
theorem signed_mixed_nonneg_of_fundamental (Q : QuaternionicStructure V)
    (c : Basis ι ℝ V) (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension)
    (L : E V →ₗ[ℝ] ℝ)
    (hfund : 0 ≤ L (QuaternionicFundamental.form Q c ^ Q.quaternionicDimension)) :
    0 ≤ L ((-(evenForm c A) ^ 2) ^ k * QuaternionicFundamental.form Q c ^
      (Q.quaternionicDimension - k)) :=
  signed_mixed_nonneg Q c A hA k hk L ((topForm_nonneg_iff Q c L).mpr hfund)

theorem formSpace_signed_mixed_nonneg (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (θ : E V) (hθ : θ ∈ formSpace Q c) (k : ℕ) (hk : k ≤ Q.quaternionicDimension)
    (L : E V →ₗ[ℝ] ℝ) (hvol : 0 ≤ L (topForm Q c)) :
    0 ≤ L ((-θ ^ 2) ^ k * QuaternionicFundamental.form Q c ^
      (Q.quaternionicDimension - k)) := by
  obtain ⟨A, hA, rfl⟩ := (formSpace_mem_iff Q c θ).mp hθ
  exact signed_mixed_nonneg Q c A hA k hk L hvol

end
end QuaternionicSymmetry.QuaternionicSpectralSign
