import Mathlib.Tactic

/-! The index contraction in Schur's lemma. This is pure finite-dimensional
algebra: a covariant derivative of an algebraic curvature tensor satisfying
second Bianchi and the derivative of the Einstein equation has constant
Einstein factor whenever the dimension is different from two. -/
namespace QuaternionicSymmetry.AlgebraicSchurContraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Abstract covariant derivative of the curvature 4-tensor. Its first
argument is the derivative direction. -/
def CurvatureDerivative (ι : Type*) := ι → ι → ι → ι → ι → ℝ

/-- The four-slot curvature tensor retains its pair symmetries under a
metric-compatible covariant derivative. -/
def PairSymmetric (T : CurvatureDerivative ι) : Prop :=
  (∀ a b c d e, T a b c d e = -T a b c e d) ∧
  (∀ a b c d e, T a b c d e = T a d e b c)

/-- A coordinate form of differential second Bianchi. -/
def SecondBianchi (T : CurvatureDerivative ι) : Prop :=
  ∀ a b c d e, T a b c d e + T b c a d e + T c a b d e = 0

/-- The covariant derivative of `Ric = λ g` in an orthonormal basis. -/
def EinsteinDerivative (T : CurvatureDerivative ι) (dlambda : ι → ℝ) : Prop :=
  ∀ a v w, (∑ i, T a i v w i) = dlambda a * if v = w then 1 else 0

/-- Contracted second Bianchi under the differentiated Einstein identity:
`(dimension - 2) dλ = 0`. -/
theorem schur_factor (T : CurvatureDerivative ι) (dlambda : ι → ℝ)
    (hpair : PairSymmetric T) (hB : SecondBianchi T)
    (hEin : EinsteinDerivative T dlambda) (a : ι) :
    ((Fintype.card ι : ℝ) - 2) * dlambda a = 0 := by
  have hfirst : (∑ j, ∑ k, T a j k j k) =
      -((Fintype.card ι : ℝ) * dlambda a) := by
    calc
      _ = ∑ j, ∑ k, -T a j k k j := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        exact hpair.1 a j k j k
      _ = -(∑ j, ∑ k, T a j k k j) := by
        simp only [Finset.sum_neg_distrib]
      _ = -(∑ k, ∑ j, T a j k k j) := by rw [Finset.sum_comm]
      _ = -(∑ k : ι, dlambda a) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        simpa using hEin a k k
      _ = _ := by simp
  have hsecond : (∑ j, ∑ k, T j k a j k) = dlambda a := by
    calc
      _ = ∑ j, dlambda j * if a = j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        exact hEin j a j
      _ = dlambda a := by simp
  have hthird : (∑ j, ∑ k, T k a j j k) = dlambda a := by
    have hp (j k : ι) := hpair.2 k a j j k
    simp_rw [hp]
    rw [Finset.sum_comm]
    calc
      _ = ∑ k, dlambda k * if a = k then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        simpa only [eq_comm] using hEin k k a
      _ = dlambda a := by simp
  have hzero : (∑ j, ∑ k, (T a j k j k + T j k a j k + T k a j j k)) = 0 := by
    simp_rw [hB a]
    simp
  simp_rw [Finset.sum_add_distrib] at hzero
  rw [hfirst, hsecond, hthird] at hzero
  linarith

/-- Schur's conclusion when the dimension is at least three. -/
theorem schur_derivative_zero (T : CurvatureDerivative ι) (dlambda : ι → ℝ)
    (hcard : 3 ≤ Fintype.card ι)
    (hpair : PairSymmetric T) (hB : SecondBianchi T)
    (hEin : EinsteinDerivative T dlambda) (a : ι) : dlambda a = 0 := by
  have hf := schur_factor T dlambda hpair hB hEin a
  have hn : (Fintype.card ι : ℝ) - 2 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (by omega : Fintype.card ι ≠ 2)
  exact (mul_eq_zero.mp hf).resolve_left hn

end QuaternionicSymmetry.AlgebraicSchurContraction
