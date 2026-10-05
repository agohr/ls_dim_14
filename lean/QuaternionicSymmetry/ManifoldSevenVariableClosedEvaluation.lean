import QuaternionicSymmetry.DimensionThirteenFourteenDensity
import QuaternionicSymmetry.ManifoldEvenClosedAlgebra
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
Reusable graded evaluation of the seven-variable polynomial ring. The
generators may be arbitrary actual closed forms of degrees
`4,4,8,12,16,20,24`, so one proof of a printed polynomial's weight applies
to every curvature normalization and every connection.
-/

namespace QuaternionicSymmetry.ManifoldSevenVariableClosedEvaluation

open QuaternionicSymmetry.ManifoldEvenClosedAlgebra
  QuaternionicSymmetry.DimensionThirteenFourteenDensity
open scoped Manifold ContDiff Topology

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

structure Generators where
  u : Grade (E := E) (M := M) 1
  p1 : Grade (E := E) (M := M) 1
  p2 : Grade (E := E) (M := M) 2
  p3 : Grade (E := E) (M := M) 3
  p4 : Grade (E := E) (M := M) 4
  p5 : Grade (E := E) (M := M) 5
  p6 : Grade (E := E) (M := M) 6

variable (g : Generators (E := E) (M := M))

noncomputable def generatorValues : Fin 7 → Total (E := E) (M := M) :=
  ![DirectSum.of _ 1 g.u, DirectSum.of _ 1 g.p1,
    DirectSum.of _ 2 g.p2, DirectSum.of _ 3 g.p3,
    DirectSum.of _ 4 g.p4, DirectSum.of _ 5 g.p5,
    DirectSum.of _ 6 g.p6]

noncomputable def evaluate : DimensionThirteenFourteenDensity.P →+*
    Total (E := E) (M := M) :=
  MvPolynomial.eval₂Hom rationalConstants (generatorValues g)

noncomputable def homogeneousForm (n : ℕ)
    (P : DimensionThirteenFourteenDensity.P) : Grade (E := E) (M := M) n :=
  DirectSum.component ℝ ℕ (Grade (E := E) (M := M)) n (evaluate g P)

private def HasGrade (n : ℕ) (P : DimensionThirteenFourteenDensity.P) : Prop :=
  ∃ a : Grade (E := E) (M := M) n,
    evaluate g P = DirectSum.of (Grade (E := E) (M := M)) n a

private theorem hasGrade_add {n : ℕ} {P R : DimensionThirteenFourteenDensity.P}
    (hP : HasGrade g n P) (hR : HasGrade g n R) : HasGrade g n (P + R) := by
  rcases hP with ⟨a, ha⟩
  rcases hR with ⟨b, hb⟩
  exact ⟨a + b, by simp [ha, hb]⟩

private theorem hasGrade_sum {ι : Type} (s : Finset ι)
    (P : ι → DimensionThirteenFourteenDensity.P) {n : ℕ}
    (h : ∀ i ∈ s, HasGrade g n (P i)) : HasGrade g n (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact hasGrade_add g (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem hasGrade_mul {m n : ℕ} {P R : DimensionThirteenFourteenDensity.P}
    (hP : HasGrade g m P) (hR : HasGrade g n R) :
    HasGrade g (m + n) (P * R) := by
  rcases hP with ⟨a, ha⟩
  rcases hR with ⟨b, hb⟩
  refine ⟨gradeMul m n a b, ?_⟩
  simp only [map_mul, ha, hb]
  exact DirectSum.of_mul_of a b

private theorem hasGrade_mul' {m n k : ℕ} {P R : DimensionThirteenFourteenDensity.P}
    (h : m + n = k) (hP : HasGrade g m P) (hR : HasGrade g n R) :
    HasGrade g k (P * R) := by
  subst k
  exact hasGrade_mul g hP hR

private theorem hasGrade_pow {m : ℕ} {P : DimensionThirteenFourteenDensity.P}
    (hP : HasGrade g m P) (k : ℕ) : HasGrade g (k * m) (P ^ k) := by
  rcases hP with ⟨a, ha⟩
  refine ⟨GradedMonoid.GMonoid.gnpow k a, ?_⟩
  simp only [map_pow, ha]
  simpa only [nsmul_eq_mul] using
    (DirectSum.ofPow (Grade (E := E) (M := M)) a k)

private theorem hasGrade_pow' {m k n : ℕ} {P : DimensionThirteenFourteenDensity.P}
    (h : k * m = n) (hP : HasGrade g m P) : HasGrade g n (P ^ k) := by
  subst n
  exact hasGrade_pow g hP k

private theorem hasGrade_C (q : ℚ) : HasGrade g 0 (MvPolynomial.C q) := by
  refine ⟨(q : ℝ), ?_⟩
  simp only [evaluate, MvPolynomial.eval₂Hom_C, rationalConstants,
    RingHom.comp_apply]
  rfl

private theorem hasGrade_C_mul {n : ℕ} (q : ℚ)
    {P : DimensionThirteenFourteenDensity.P} (hP : HasGrade g n P) :
    HasGrade g n (MvPolynomial.C q * P) := by
  simpa only [Nat.zero_add] using hasGrade_mul g (hasGrade_C g q) hP

private theorem hasGrade_u : HasGrade g 1 u := by
  refine ⟨g.u, ?_⟩
  simp [evaluate, u, generatorValues]

private theorem hasGrade_p1 : HasGrade g 1 p1 := by
  refine ⟨g.p1, ?_⟩
  simp [evaluate, p1, generatorValues]

private theorem hasGrade_p2 : HasGrade g 2 p2 := by
  refine ⟨g.p2, ?_⟩
  simp [evaluate, p2, generatorValues]

private theorem hasGrade_p3 : HasGrade g 3 p3 := by
  refine ⟨g.p3, ?_⟩
  simp [evaluate, p3, generatorValues]

private theorem hasGrade_p4 : HasGrade g 4 p4 := by
  refine ⟨g.p4, ?_⟩
  simp [evaluate, p4, generatorValues]

private theorem hasGrade_p5 : HasGrade g 5 p5 := by
  refine ⟨g.p5, ?_⟩
  simp [evaluate, p5, generatorValues]

private theorem hasGrade_p6 : HasGrade g 6 p6 := by
  refine ⟨g.p6, ?_⟩
  simp [evaluate, p6, generatorValues]

private theorem hasGrade_u_pow (k : ℕ) : HasGrade g k (u ^ k) := by
  simpa only [Nat.mul_one] using hasGrade_pow g (hasGrade_u g) k

private theorem hasGrade_p1_pow (k : ℕ) : HasGrade g k (p1 ^ k) := by
  simpa only [Nat.mul_one] using hasGrade_pow g (hasGrade_p1 g) k

/-- Weighted degree of each independent polynomial generator. -/
def slotGrade : Fin 7 → ℕ := ![1, 1, 2, 3, 4, 5, 6]

private theorem hasGrade_X (i : Fin 7) :
    HasGrade g (slotGrade i) (MvPolynomial.X i) := by
  fin_cases i
  all_goals first
    | exact hasGrade_u g
    | exact hasGrade_p1 g
    | exact hasGrade_p2 g
    | exact hasGrade_p3 g
    | exact hasGrade_p4 g
    | exact hasGrade_p5 g
    | exact hasGrade_p6 g

noncomputable def monomial (e : Fin 7 → ℕ) : DimensionThirteenFourteenDensity.P :=
  ∏ i : Fin 7, MvPolynomial.X i ^ e i

def totalWeight (e : Fin 7 → ℕ) : ℕ :=
  ∑ i : Fin 7, e i * slotGrade i

/-- Every monomial evaluates in its declared weighted de Rham grade. -/
private theorem hasGrade_prod (s : Finset (Fin 7)) (e : Fin 7 → ℕ) :
    HasGrade g (∑ i ∈ s, e i * slotGrade i)
      (∏ i ∈ s, MvPolynomial.X i ^ e i) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty, Finset.prod_empty] using hasGrade_C g 1
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      exact hasGrade_mul g (hasGrade_pow g (hasGrade_X g i) (e i)) ih

private theorem hasGrade_monomial (e : Fin 7 → ℕ) :
    HasGrade g (totalWeight e) (monomial e) := by
  exact hasGrade_prod g Finset.univ e

/-- Weighted homogeneity in the polynomial ring forces the corresponding
evaluation to lie in the same actual de Rham grade. -/
theorem pureGrade_of_weighted {n : ℕ} {P : DimensionThirteenFourteenDensity.P}
    (hP : MvPolynomial.IsWeightedHomogeneous slotGrade P n) :
    ∃ a : Grade (E := E) (M := M) n,
      evaluate g P = DirectSum.of (Grade (E := E) (M := M)) n a := by
  classical
  rw [MvPolynomial.as_sum (p := P)]
  apply hasGrade_sum g
  intro d hd
  rw [MvPolynomial.monomial_eq, Finsupp.prod]
  have hw : Finsupp.weight slotGrade d = n :=
    hP (MvPolynomial.mem_support_iff.mp hd)
  have hprod := hasGrade_prod g d.support d
  have hweight : (∑ i ∈ d.support, d i * slotGrade i) = n := by
    simpa only [Finsupp.weight_apply, Finsupp.sum] using hw
  rw [hweight] at hprod
  exact hasGrade_C_mul g (MvPolynomial.coeff d P) hprod

end QuaternionicSymmetry.ManifoldSevenVariableClosedEvaluation
