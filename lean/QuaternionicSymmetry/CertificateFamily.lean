import QuaternionicSymmetry.CertificateFunctionalBounds
import QuaternionicSymmetry.Arithmetic

/-! The nine finite certificates in a single dimension-indexed family. -/

namespace QuaternionicSymmetry.CertificateFamily

open AlgebraCertificates CertificateFunctionalBounds

noncomputable section

def polynomial (n : ℕ) : P :=
  match n with
  | 2 => K₂
  | 3 => K₃
  | 4 => K₄
  | 5 => K₅
  | 6 => K₆
  | 7 => K₇
  | 8 => K₈
  | 9 => K₉
  | 10 => K₁₀
  | _ => 0

theorem functional_lower_bound (L : P →ₗ[ℚ] ℝ) (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 10)
    (hZ : ∀ k : ℕ, k ≤ n → 0 ≤ L (Z₁ ^ k * U ^ (n - k)))
    (hF₂ : 2 ≤ n → 0 ≤ L (F₂ * U ^ (n - 2)))
    (hF₃ : 3 ≤ n → 0 ≤ L (F₃ * U ^ (n - 3)))
    (hF₄ : 4 ≤ n → 0 ≤ L (F₄ * U ^ (n - 4)))
    (hM₂₁ : 2 ≤ n → 0 ≤ L (M₂₁ (2 * n + 2) * U ^ (n - 2)))
    (hM₃₁ : 3 ≤ n → 0 ≤ L (M₃₁ (2 * n + 2) * U ^ (n - 3)))
    (hM₃₂ : 3 ≤ n → 0 ≤ L (M₃₂ (2 * n + 2) * U ^ (n - 3))) :
    (scalarCoefficient n : ℝ) * L (U ^ n) ≤ L (polynomial n) := by
  have hz₁ : 0 ≤ L (Z₁ * U ^ (n - 1)) := by
    simpa only [pow_one] using hZ 1 (by omega)
  interval_cases n
  · simpa only [polynomial, scalarCoefficient, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceMul, Nat.cast_ofNat] using (lower_bound_2 (L := L))
  · norm_num only [polynomial, scalarCoefficient, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat]
    exact lower_bound_3 hz₁
  · norm_num only [polynomial, scalarCoefficient, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat]
    exact lower_bound_4 hz₁
  · norm_num only [polynomial, scalarCoefficient, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat]
    exact lower_bound_5 hz₁ (hF₂ (by decide))
  · norm_num only [polynomial, scalarCoefficient, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat]
    exact lower_bound_6 hz₁ (hF₂ (by decide))
  · norm_num only [polynomial, scalarCoefficient, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat]
    apply lower_bound_7 hz₁ _ (hZ 2 (by decide)) (hF₃ (by decide))
    convert hM₂₁ (by decide) using 1; norm_num
  · norm_num only [polynomial, scalarCoefficient, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat]
    apply lower_bound_8 hz₁ _ (hZ 2 (by decide)) (hF₃ (by decide))
    convert hM₂₁ (by decide) using 1; norm_num
  · norm_num only [polynomial, scalarCoefficient, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat]
    apply lower_bound_9 hz₁ _ (hZ 2 (by decide)) _ _ (hZ 3 (by decide)) (hF₄ (by decide))
    · convert hM₂₁ (by decide) using 1; norm_num
    · convert hM₃₁ (by decide) using 1; norm_num
    · convert hM₃₂ (by decide) using 1; norm_num
  · norm_num only [polynomial, scalarCoefficient, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat]
    apply lower_bound_10 hz₁ _ (hZ 2 (by decide)) _ _ (hZ 3 (by decide)) (hF₄ (by decide))
    · convert hM₂₁ (by decide) using 1; norm_num
    · convert hM₃₁ (by decide) using 1; norm_num
    · convert hM₃₂ (by decide) using 1; norm_num

end
end QuaternionicSymmetry.CertificateFamily
