import QuaternionicSymmetry.FiniteRankOneAbelian
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.Noetherian.Basic

/-! A nonzero integral degree map on a torsion-free rank-one group is
injective. Thus its finite generation follows from its embedding in ℤ;
one need not assume integral cohomology finite generation separately in
the degree-two Picard argument. The rank and actual degree map remain
explicit hypotheses, not inferred from a finite-dimensional surrogate. -/

namespace QuaternionicSymmetry.RankOneDegreeInjection

open FiniteRankOneAbelian
noncomputable section

variable {G : Type*} [AddCommGroup G] [IsAddTorsionFree G]

theorem degree_injective (hRank : Module.finrank ℤ G = 1)
    (degree : G →+ ℤ) (x : G) (hx : degree x ≠ 0) :
    Function.Injective degree := by
  apply (injective_iff_map_eq_zero degree).mpr
  intro y hy
  by_contra hyne
  have hli : LinearIndependent ℤ (![y, x] : Fin 2 → G) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have hrel : a 0 • y + a 1 • x = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using ha
    have hdeg : a 1 * degree x = 0 := by
      simpa [hy] using congrArg degree hrel
    have ha1 : a 1 = 0 := (mul_eq_zero.mp hdeg).resolve_right hx
    rw [ha1, zero_smul, add_zero] at hrel
    have ha0 : a 0 = 0 := (smul_eq_zero.mp hrel).resolve_right hyne
    fin_cases i
    · exact ha0
    · exact ha1
  have hc := hli.cardinal_lift_le_rank
  have hr : Module.rank ℤ G = 1 :=
    Module.rank_eq_one_iff_finrank_eq_one.mpr hRank
  rw [hr] at hc
  norm_num at hc

theorem finite_of_degree (hRank : Module.finrank ℤ G = 1)
    (degree : G →+ ℤ) (x : G) (hx : degree x ≠ 0) :
    Module.Finite ℤ G :=
  Module.Finite.of_injective degree.toIntLinearMap
    (degree_injective hRank degree x hx)

/-- Both the finite-generation and coordinate-algebra steps are now
internal, leaving just torsion-freeness, rank one and a degree-two class. -/
theorem exists_coordinate_one_or_two_of_degree
    (hRank : Module.finrank ℤ G = 1)
    (degree : G →+ ℤ) (x : G) (hDegree : degree x = 2) :
    ∃ e : G ≃+ ℤ, e x = 1 ∨ e x = 2 := by
  have hx : degree x ≠ 0 := by omega
  letI := finite_of_degree hRank degree x hx
  exact exists_integer_coordinate_one_or_two hRank degree x hDegree

end
end QuaternionicSymmetry.RankOneDegreeInjection
