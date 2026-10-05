import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.Int.Basic

/-! The elementary integral algebra in the Picard-generator argument.
Finite generation is explicit: torsion-freeness and rank one alone would
not identify a group with ℤ (the additive group of ℚ is a counterexample).
The degree homomorphism below is genuine additive data; its geometric
construction and its value on the contact line are not asserted here. -/

namespace QuaternionicSymmetry.FiniteRankOneAbelian

noncomputable section

variable (G : Type*) [AddCommGroup G]

def integerEquiv [IsAddTorsionFree G] [Module.Finite ℤ G]
    (hRank : Module.finrank ℤ G = 1) : G ≃+ ℤ :=
  (Module.nonempty_linearEquiv_of_finrank_eq_one hRank).some.symm.toAddEquiv

variable {G}

theorem coordinate_dvd_degree (e : G ≃+ ℤ) (degree : G →+ ℤ) (x : G) :
    e x ∣ degree x := by
  refine ⟨degree (e.symm 1), ?_⟩
  have hx : (e x) • e.symm 1 = x := by
    apply e.injective
    simp
  have h := congrArg degree hx
  simpa only [map_zsmul, zsmul_eq_mul] using h.symm

/-- Orient any integer coordinate so the degree-two element has positive
coordinate. Its coordinate is one or two, with no positivity black box. -/
theorem exists_coordinate_one_or_two (e : G ≃+ ℤ)
    (degree : G →+ ℤ) (x : G) (hDegree : degree x = 2) :
    ∃ f : G ≃+ ℤ, f x = 1 ∨ f x = 2 := by
  have hdvd : e x ∣ (2 : ℤ) := hDegree ▸ coordinate_dvd_degree e degree x
  have habs : (e x).natAbs ≤ 2 := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdvd (by norm_num : (2 : ℤ) ≠ 0)
  have hne : e x ≠ 0 := by
    intro hzero
    rw [hzero, zero_dvd_iff] at hdvd
    norm_num at hdvd
  have hcases : e x = 1 ∨ e x = 2 ∨ e x = -1 ∨ e x = -2 := by omega
  rcases hcases with h | h | h | h
  · exact ⟨e, Or.inl h⟩
  · exact ⟨e, Or.inr h⟩
  · refine ⟨e.trans (AddEquiv.neg ℤ), Or.inl ?_⟩
    change -(e x) = 1
    omega
  · refine ⟨e.trans (AddEquiv.neg ℤ), Or.inr ?_⟩
    change -(e x) = 2
    omega

theorem exists_integer_coordinate_one_or_two
    [IsAddTorsionFree G] [Module.Finite ℤ G]
    (hRank : Module.finrank ℤ G = 1)
    (degree : G →+ ℤ) (x : G) (hDegree : degree x = 2) :
    ∃ f : G ≃+ ℤ, f x = 1 ∨ f x = 2 :=
  exists_coordinate_one_or_two (integerEquiv G hRank) degree x hDegree

/-- The coordinate-one branch says the original element itself freely
generates the whole group, not merely a finite-index subgroup. -/
theorem zsmul_bijective_of_coordinate_one (e : G ≃+ ℤ) (x : G)
    (hx : e x = 1) : Function.Bijective (fun k : ℤ => k • x) := by
  constructor
  · intro k l h
    have h' := congrArg e h
    simpa only [map_zsmul, hx, zsmul_eq_mul, mul_one] using h'
  · intro y
    refine ⟨e y, e.injective ?_⟩
    simp [hx]

end
end QuaternionicSymmetry.FiniteRankOneAbelian
