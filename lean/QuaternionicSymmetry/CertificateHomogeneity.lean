import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import QuaternionicSymmetry.AlgebraCertificates

/-!
  Weighted-degree bookkeeping for the universal certificate polynomials.

  The variables `u,z₁,z₂,z₃,z₄` have weights `1,1,2,3,4`.  Thus evaluating
  them in degree `4,4,8,12,16` forms gives the expected total degree `4n`
  for the weight-`n` certificate polynomials.  This file records only the
  universal polynomial calculation; it makes no geometric assertion about
  the forms being substituted.
-/

namespace QuaternionicSymmetry
namespace CertificateHomogeneity

noncomputable section

open AlgebraCertificates

/-- The weights of `u,z₁,z₂,z₃,z₄`, in the order of the universal variables. -/
def weights : Fin 5 → ℕ := ![1, 1, 2, 3, 4]

/-- Weighted homogeneity in the universal rational polynomial ring. -/
def WH (p : P) (n : ℕ) : Prop := MvPolynomial.IsWeightedHomogeneous weights p n

private theorem U_wh : WH U 1 := by
  simpa [WH, U, weights] using
    (MvPolynomial.isWeightedHomogeneous_X (R := ℚ) weights (0 : Fin 5))

private theorem Z₁_wh : WH Z₁ 1 := by
  simpa [WH, Z₁, weights] using
    (MvPolynomial.isWeightedHomogeneous_X (R := ℚ) weights (1 : Fin 5))

private theorem Z₂_wh : WH Z₂ 2 := by
  simpa [WH, Z₂, weights] using
    (MvPolynomial.isWeightedHomogeneous_X (R := ℚ) weights (2 : Fin 5))

private theorem Z₃_wh : WH Z₃ 3 := by
  simpa [WH, Z₃, weights] using
    (MvPolynomial.isWeightedHomogeneous_X (R := ℚ) weights (3 : Fin 5))

private theorem Z₄_wh : WH Z₄ 4 := by
  simpa [WH, Z₄, weights] using
    (MvPolynomial.isWeightedHomogeneous_X (R := ℚ) weights (4 : Fin 5))

private theorem c_mul_wh {p : P} {n : ℕ} (a : ℚ) (hp : WH p n) : WH (c a * p) n := by
  simpa [WH, c] using hp.C_mul a

private theorem neg_wh {p : P} {n : ℕ} (hp : WH p n) : WH (-p) n := by
  intro d hd
  apply hp
  intro h
  apply hd
  simp [h]

private theorem sub_wh {p q : P} {n : ℕ} (hp : WH p n) (hq : WH q n) : WH (p - q) n := by
  rw [sub_eq_add_neg]
  exact hp.add (neg_wh hq)

private theorem U_pow_wh (k : ℕ) : WH (U ^ k) k := by
  simpa [WH] using U_wh.pow k

private theorem Z₁_pow_wh (k : ℕ) : WH (Z₁ ^ k) k := by
  simpa [WH] using Z₁_wh.pow k

theorem b₁_wh (n : ℚ) : WH (b₁ n) 1 := by
  unfold b₁
  exact (c_mul_wh _ U_wh).add (c_mul_wh _ Z₁_wh)

theorem b₂_wh (n : ℚ) : WH (b₂ n) 2 := by
  unfold b₂
  refine (sub_wh ?_ ?_).add (c_mul_wh _ Z₂_wh)
  · exact c_mul_wh _ (U_pow_wh 2)
  · simpa [mul_assoc] using c_mul_wh _ (U_wh.mul Z₁_wh)

theorem b₃_wh (n : ℚ) : WH (b₃ n) 3 := by
  unfold b₃
  apply MvPolynomial.IsWeightedHomogeneous.add
  apply sub_wh
  · apply MvPolynomial.IsWeightedHomogeneous.add
    · exact c_mul_wh _ (U_pow_wh 3)
    · simpa [mul_assoc] using c_mul_wh _ ((U_pow_wh 2).mul Z₁_wh)
  · simpa [mul_assoc] using c_mul_wh _ (U_wh.mul Z₂_wh)
  · exact c_mul_wh _ Z₃_wh

theorem b₄_wh (n : ℚ) : WH (b₄ n) 4 := by
  unfold b₄
  apply MvPolynomial.IsWeightedHomogeneous.add
  apply sub_wh
  · apply MvPolynomial.IsWeightedHomogeneous.add
    · apply sub_wh
      · exact c_mul_wh _ (U_pow_wh 4)
      · simpa [mul_assoc] using c_mul_wh _ ((U_pow_wh 3).mul Z₁_wh)
    · simpa [mul_assoc] using c_mul_wh _ ((U_pow_wh 2).mul Z₂_wh)
  · simpa [mul_assoc] using c_mul_wh _ (U_wh.mul Z₃_wh)
  · exact c_mul_wh _ Z₄_wh

theorem A₀_wh : WH A₀ 0 := by
  simpa [A₀, WH] using MvPolynomial.isWeightedHomogeneous_one (R := ℚ) weights

theorem A₁_wh (n : ℚ) : WH (A₁ n) 1 := by
  exact b₁_wh n

theorem A₂_wh (n : ℚ) : WH (A₂ n) 2 := by
  unfold A₂
  exact (b₂_wh n).add (c_mul_wh _ (by simpa [WH] using (b₁_wh n).pow 2))

theorem A₃_wh (n : ℚ) : WH (A₃ n) 3 := by
  unfold A₃
  refine ((b₃_wh n).add ((b₁_wh n).mul (b₂_wh n))).add ?_
  exact c_mul_wh _ (by simpa [WH] using (b₁_wh n).pow 3)

theorem A₄_wh (n : ℚ) : WH (A₄ n) 4 := by
  unfold A₄
  refine (((b₄_wh n).add ((b₁_wh n).mul (b₃_wh n))).add ?_).add ?_ |>.add ?_
  · exact c_mul_wh _ (by simpa [WH] using (b₂_wh n).pow 2)
  · have h : WH (b₁ n ^ 2) 2 := by simpa [WH] using (b₁_wh n).pow 2
    simpa [mul_assoc] using c_mul_wh _ (h.mul (b₂_wh n))
  · exact c_mul_wh _ (by simpa [WH] using (b₁_wh n).pow 4)

theorem F₂_wh : WH F₂ 2 := by
  unfold F₂
  exact (c_mul_wh _ (Z₁_pow_wh 2)).add (c_mul_wh _ Z₂_wh)

theorem F₃_wh : WH F₃ 3 := by
  unfold F₃
  refine ((c_mul_wh _ (Z₁_pow_wh 3)).add ?_).add (c_mul_wh _ Z₃_wh)
  simpa [mul_assoc] using c_mul_wh _ (Z₁_wh.mul Z₂_wh)

theorem F₄_wh : WH F₄ 4 := by
  unfold F₄
  refine ((((c_mul_wh _ (Z₁_pow_wh 4)).add ?_).add ?_).add ?_).add (c_mul_wh _ Z₄_wh)
  · simpa [mul_assoc] using c_mul_wh _ ((Z₁_pow_wh 2).mul Z₂_wh)
  · exact c_mul_wh _ (by simpa [WH] using Z₂_wh.pow 2)
  · simpa [mul_assoc] using c_mul_wh _ (Z₁_wh.mul Z₃_wh)

theorem M₂₁_wh (r : ℚ) : WH (M₂₁ r) 2 := by
  unfold M₂₁
  exact c_mul_wh _ ((Z₁_pow_wh 2).add Z₂_wh)

theorem M₃₁_wh (r : ℚ) : WH (M₃₁ r) 3 := by
  unfold M₃₁
  refine c_mul_wh _ ((Z₁_pow_wh 3).add ?_ |>.add ?_)
  · simpa [mul_assoc] using c_mul_wh _ (Z₁_wh.mul Z₂_wh)
  · exact c_mul_wh _ Z₃_wh

theorem M₃₂_wh (r : ℚ) : WH (M₃₂ r) 3 := by
  unfold M₃₂
  refine c_mul_wh _ ((c_mul_wh _ (Z₁_pow_wh 3)).add ?_ |>.add ?_)
  · simpa [mul_assoc] using c_mul_wh _ (Z₁_wh.mul Z₂_wh)
  · exact c_mul_wh _ Z₃_wh

private theorem scaled_UA_wh (a : ℚ) (i j : ℕ) {p : P} (hp : WH p j) :
    WH (c a * U ^ i * p) (i + j) := by
  simpa [mul_assoc] using c_mul_wh a ((U_pow_wh i).mul hp)

/-- The second universal certificate has weighted degree two. -/
theorem K₂_wh : WH K₂ 2 := by
  unfold K₂
  exact scaled_UA_wh 16 2 0 A₀_wh

/-- The third universal certificate has weighted degree three. -/
theorem K₃_wh : WH K₃ 3 := by
  unfold K₃
  exact (scaled_UA_wh 32 2 1 (A₁_wh 3)).add (scaled_UA_wh (112 / 3) 3 0 A₀_wh)

/-- The fourth universal certificate has weighted degree four. -/
theorem K₄_wh : WH K₄ 4 := by
  unfold K₄
  exact (scaled_UA_wh 64 3 1 (A₁_wh 4)).add (scaled_UA_wh 64 4 0 A₀_wh)

/-- The fifth universal certificate has weighted degree five. -/
theorem K₅_wh : WH K₅ 5 := by
  unfold K₅
  exact ((scaled_UA_wh 128 3 2 (A₂_wh 5)).add
    (scaled_UA_wh 192 4 1 (A₁_wh 5))).add (scaled_UA_wh (1936 / 15) 5 0 A₀_wh)

/-- The sixth universal certificate has weighted degree six. -/
theorem K₆_wh : WH K₆ 6 := by
  unfold K₆
  exact ((scaled_UA_wh 256 4 2 (A₂_wh 6)).add
    (scaled_UA_wh (1024 / 3) 5 1 (A₁_wh 6))).add (scaled_UA_wh (9728 / 45) 6 0 A₀_wh)

/-- The seventh universal certificate has weighted degree seven. -/
theorem K₇_wh : WH K₇ 7 := by
  unfold K₇
  exact (((scaled_UA_wh 512 4 3 (A₃_wh 7)).add
    (scaled_UA_wh (2816 / 3) 5 2 (A₂_wh 7))).add
    (scaled_UA_wh (35776 / 45) 6 1 (A₁_wh 7))).add
    (scaled_UA_wh (79136 / 189) 7 0 A₀_wh)

/-- The eighth universal certificate has weighted degree eight. -/
theorem K₈_wh : WH K₈ 8 := by
  unfold K₈
  exact (((scaled_UA_wh 1024 5 3 (A₃_wh 8)).add
    (scaled_UA_wh (5120 / 3) 6 2 (A₂_wh 8))).add
    (scaled_UA_wh (4096 / 3) 7 1 (A₁_wh 8))).add
    (scaled_UA_wh (44032 / 63) 8 0 A₀_wh)

/-- The ninth universal certificate has weighted degree nine. -/
theorem K₉_wh : WH K₉ 9 := by
  unfold K₉
  exact ((((scaled_UA_wh 2048 5 4 (A₄_wh 9)).add
    (scaled_UA_wh (13312 / 3) 6 3 (A₃_wh 9))).add
    (scaled_UA_wh (13568 / 3) 7 2 (A₂_wh 9))).add
    (scaled_UA_wh (916096 / 315) 8 1 (A₁_wh 9))).add
    (scaled_UA_wh (3777808 / 2835) 9 0 A₀_wh)

/-- The tenth universal certificate has weighted degree ten. -/
theorem K₁₀_wh : WH K₁₀ 10 := by
  unfold K₁₀
  exact ((((scaled_UA_wh 4096 6 4 (A₄_wh 10)).add
    (scaled_UA_wh 8192 7 3 (A₃_wh 10))).add
    (scaled_UA_wh (118784 / 15) 8 2 (A₂_wh 10))).add
    (scaled_UA_wh (4661248 / 945) 9 1 (A₁_wh 10))).add
    (scaled_UA_wh (1503232 / 675) 10 0 A₀_wh)

end
end CertificateHomogeneity
end QuaternionicSymmetry
