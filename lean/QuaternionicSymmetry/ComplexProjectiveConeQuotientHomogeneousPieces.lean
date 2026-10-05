import QuaternionicSymmetry.ComplexProjectiveConeHomogeneousIdealInput
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Candidate degree pieces of the actual homogeneous cone quotient.
These are images of Mathlib's homogeneous polynomial submodules under
the literal quotient map. Direct-sum decomposition remains to prove. -/

namespace QuaternionicSymmetry.ComplexProjectiveConeQuotientHomogeneousPieces

open ComplexProjectiveTopology ComplexProjectiveDiagonalVanishingIdeal
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

def quotientPiece (A : Set (Space d)) (n : ℕ) :
    Submodule ℂ
      (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) :=
  (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ n).map
    (Ideal.Quotient.mkₐ ℂ (vanishingIdeal A)).toLinearMap

theorem mem_quotientPiece_iff (A : Set (Space d)) (n : ℕ)
    (q : MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) :
    q ∈ quotientPiece A n ↔
      ∃ p : MvPolynomial (Fin (d + 1)) ℂ,
        p.IsHomogeneous n ∧ Ideal.Quotient.mk (vanishingIdeal A) p = q := by
  simp [quotientPiece, Submodule.mem_map, MvPolynomial.mem_homogeneousSubmodule,
    Ideal.Quotient.mkₐ_eq_mk]

theorem one_mem_quotientPiece_zero (A : Set (Space d)) :
    (1 : MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) ∈
      quotientPiece A 0 := by
  rw [mem_quotientPiece_iff]
  exact ⟨1, MvPolynomial.isHomogeneous_one _ _, by simp⟩

theorem mul_mem_quotientPiece (A : Set (Space d))
    {m n : ℕ}
    {x y : MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A}
    (hx : x ∈ quotientPiece A m) (hy : y ∈ quotientPiece A n) :
    x * y ∈ quotientPiece A (m + n) := by
  obtain ⟨p, hp, rfl⟩ := (mem_quotientPiece_iff A m x).mp hx
  obtain ⟨q, hq, rfl⟩ := (mem_quotientPiece_iff A n y).mp hy
  rw [mem_quotientPiece_iff]
  exact ⟨p * q, hp.mul hq, by simp⟩

theorem iSup_quotientPiece_eq_top (A : Set (Space d)) :
    (⨆ n : ℕ, quotientPiece A n) = ⊤ := by
  classical
  apply top_le_iff.mp
  intro q hq
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ
  let f : MvPolynomial (Fin (d + 1)) ℂ →ₗ[ℂ]
      (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) :=
    (Ideal.Quotient.mkₐ ℂ (vanishingIdeal A)).toLinearMap
  change f p ∈ ⨆ n : ℕ, quotientPiece A n
  rw [← DirectSum.sum_support_decompose 𝒜 p, map_sum]
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.mem_iSup_of_mem n
  change f ((DirectSum.decompose 𝒜 p n : 𝒜 n) :
    MvPolynomial (Fin (d + 1)) ℂ) ∈ quotientPiece A n
  exact ⟨_, SetLike.coe_mem _, rfl⟩

theorem quotientPiece_iSupIndep (A : Set (Space d))
    (hA : ComplexProjectivePolynomialLocus.HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) :
    iSupIndep (quotientPiece A) := by
  classical
  apply (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero (quotientPiece A)).2
  intro s v hv hsum i hi
  let P := MvPolynomial (Fin (d + 1)) ℂ
  let I := vanishingIdeal A
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ
  let p : ℕ → P := fun n =>
    if hn : n ∈ s then
      Classical.choose ((mem_quotientPiece_iff A n (v n)).mp (hv n hn))
    else 0
  have hpn (n : ℕ) (hn : n ∈ s) :
      p n ∈ 𝒜 n ∧ Ideal.Quotient.mk I (p n) = v n := by
    simp only [p, dif_pos hn]
    exact (Classical.choose_spec ((mem_quotientPiece_iff A n (v n)).mp (hv n hn)))
  have hsumI : (∑ n ∈ s, p n) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sum]
    calc
      (∑ n ∈ s, Ideal.Quotient.mk I (p n)) = ∑ n ∈ s, v n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (hpn n hn).2
      _ = 0 := hsum
  have hprojI : GradedRing.proj 𝒜 i (∑ n ∈ s, p n) ∈ I :=
    (ComplexProjectiveAffineConeHomogeneousIdeal.vanishingIdeal_isHomogeneous
      A hA hNonempty) i hsumI
  have hproj : GradedRing.proj 𝒜 i (∑ n ∈ s, p n) = p i := by
    rw [map_sum, Finset.sum_eq_single i]
    · exact (DirectSum.decompose_of_mem_same 𝒜 (hpn i hi).1)
    · intro n hn hni
      exact DirectSum.decompose_of_mem_ne 𝒜 (hpn n hn).1 hni
    · intro hni
      exact (hni hi).elim
  rw [hproj] at hprojI
  rw [← (hpn i hi).2]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hprojI

end
end QuaternionicSymmetry.ComplexProjectiveConeQuotientHomogeneousPieces
