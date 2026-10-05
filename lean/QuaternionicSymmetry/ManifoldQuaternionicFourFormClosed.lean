import QuaternionicSymmetry.ManifoldQuaternionicFourFormLocalCalculus
import QuaternionicSymmetry.ContinuousWedgeLeibniz
import QuaternionicSymmetry.ContinuousWedgeAssocComparison
import QuaternionicSymmetry.ContinuousWedgeGradedSwap
import QuaternionicSymmetry.LocalPolynomialTransgressionIntegral

/-! Closure of the genuine global quaternionic fundamental four-form. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourFormClosed

open QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeShuffle
  QuaternionicSymmetry.ContinuousWedgeLeibniz
  QuaternionicSymmetry.ManifoldQuaternionicFourForm
  QuaternionicSymmetry.ManifoldQuaternionicFourFormGluing
  QuaternionicSymmetry.ManifoldQuaternionicFourFormLocalCalculus
  QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
  QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold Topology ContDiff

noncomputable section

private theorem wedge_one_two_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : E [⋀^Fin 1]→L[ℝ] ℝ)
    (β : E [⋀^Fin 2]→L[ℝ] ℝ) (u v w : E) :
    wedge (ContinuousLinearMap.mul ℝ ℝ) α β ![u, v, w] =
      α ![u] * β ![v, w] - α ![v] * β ![u, w] +
        α ![w] * β ![u, v] := by
  let f : E → (Fin 2 → E) → ℝ := fun z q => α ![z] * β q
  have hf (z : E) (q : Fin 2 → E) (τ : Equiv.Perm (Fin 2)) :
      f z (q ∘ τ) = (Equiv.Perm.sign τ : ℤ) • f z q := by
    simp only [f]
    rw [show β (q ∘ τ) = (Equiv.Perm.sign τ : ℤ) • β q from
      β.toAlternatingMap.map_perm q τ]
    simp only [zsmul_eq_mul]
    ring
  have hfull := fullAlternation_eq_factorial_insertion f hf ![u, v, w]
  rw [wedge_apply]
  have hargs (σ : Equiv.Perm (Fin 3)) :
      ((ContinuousLinearMap.mul ℝ ℝ)
        (α (![u, v, w] ∘ σ ∘ (finSumFinEquiv (m := 1) (n := 2)) ∘ Sum.inl)))
        (β (![u, v, w] ∘ σ ∘ (finSumFinEquiv (m := 1) (n := 2)) ∘ Sum.inr)) =
      f (![u, v, w] (σ 0)) (fun j => ![u, v, w] (σ j.succ)) := by
    have hleft : (![u, v, w] ∘ σ ∘ (finSumFinEquiv (m := 1) (n := 2)) ∘ Sum.inl) =
        ![![u, v, w] (σ 0)] := by
      funext j
      fin_cases j
      rfl
    have hright : (![u, v, w] ∘ σ ∘ (finSumFinEquiv (m := 1) (n := 2)) ∘ Sum.inr) =
        (fun j => ![u, v, w] (σ j.succ)) := by
      funext j
      fin_cases j <;> rfl
    simp only [hleft, hright, f]
    rfl
  simp_rw [hargs]
  simp only [Units.smul_def]
  rw [hfull]
  simp only [Nat.factorial_two, Nat.factorial_one, one_mul,
    Nat.cast_ofNat, zsmul_eq_mul, smul_eq_mul]
  have h0 : (0 : Fin 3).removeNth ![u, v, w] = ![v, w] := by
    ext j
    fin_cases j <;> rfl
  have h1 : (1 : Fin 3).removeNth ![u, v, w] = ![u, w] := by
    ext j
    fin_cases j <;> rfl
  have h2 : (2 : Fin 3).removeNth ![u, v, w] = ![u, v] := by
    ext j
    fin_cases j <;> rfl
  rw [Fin.sum_univ_three]
  simp only [h0, h1, h2]
  norm_num [f]
  simp only [Matrix.cons_val_two]
  rw [show Matrix.vecHead (Matrix.vecTail ![v, w]) = w from rfl]
  ring

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)


def inducedOneForm (p : M) (y : E) (s t : Fin 3) :
    E [⋀^Fin 1]→L[ℝ] ℝ :=
  LocalConnectionForms.oneFormMap
    ((ContinuousLinearMap.proj s).comp
      (((ContinuousLinearMap.apply ℝ (Fin 3 → ℝ))
        (Pi.basisFun ℝ (Fin 3) t)).comp (inducedForm Q D p y)))

theorem inducedOneForm_apply (p : M) (y u : E) (s t : Fin 3) :
    inducedOneForm Q D p y s t ![u] =
      ManifoldQuaternionicFourFormConnection.inducedMatrix Q D p y u s t := by
  rfl

def localKahlerField (p : M) (t : Fin 3) (y : E) :
    E [⋀^Fin 2]→L[ℝ] ℝ :=
  chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ, E) p).symm y) t

theorem extDeriv_localKahler (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (t : Fin 3) :
    extDeriv (localKahlerField Q p t) y =
      ∑ s : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ)
        (inducedOneForm Q D p y s t) (localKahlerField Q p s y) := by
  ext v
  have hv : v = ![v 0, v 1, v 2] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  change (extDeriv (fun z => chartKahler Q (achart E p)
      ((extChartAt 𝓘(ℝ, E) p).symm z) t) y) ![v 0, v 1, v 2] = _
  rw [extDeriv_chartKahler_induced Q D p y hy t (v 0) (v 1) (v 2)]
  rw [ContinuousAlternatingMap.sum_apply]
  simp_rw [wedge_one_two_apply, inducedOneForm_apply]
  simp only [localKahlerField]
  have hswap (s : Fin 3) :
      chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ, E) p).symm y) s
        ![v 2, v 0] =
        -chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ, E) p).symm y) s
          ![v 0, v 2] := by
    have hvec : ![v 0, v 2] ∘ (Equiv.swap (0 : Fin 2) 1) = ![v 2, v 0] := by
      funext j
      fin_cases j <;> rfl
    simpa only [hvec] using
      (chartKahler Q (achart E p)
        ((extChartAt 𝓘(ℝ, E) p).symm y) s).toAlternatingMap.map_swap
          ![v 0, v 2] (by decide : (0 : Fin 2) ≠ 1)
  simp_rw [hswap]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_neg, Finset.sum_neg_distrib]
  abel

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem wedge_assoc_one_two_two
    (α : E [⋀^Fin 1]→L[ℝ] ℝ)
    (β γ : E [⋀^Fin 2]→L[ℝ] ℝ) :
    wedge (ContinuousLinearMap.mul ℝ ℝ)
      (wedge (ContinuousLinearMap.mul ℝ ℝ) α β) γ =
    wedge (ContinuousLinearMap.mul ℝ ℝ) α
      (wedge (ContinuousLinearMap.mul ℝ ℝ) β γ) := by
  ext v
  simpa [Function.comp_def] using
    (QuaternionicSymmetry.ContinuousWedgeAssocComparison.wedge_assoc_apply
      (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
      (by intros; simp [mul_assoc]) α β γ v)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem wedge_swap_two_two
    (β γ : E [⋀^Fin 2]→L[ℝ] ℝ) :
    wedge (ContinuousLinearMap.mul ℝ ℝ) β γ =
    wedge (ContinuousLinearMap.mul ℝ ℝ) γ β := by
  ext v
  have h := QuaternionicSymmetry.ContinuousWedgeGradedSwap.wedge_swap
    (p := 2) (q := 2) (by omega) (by omega) γ β v
  norm_num at h
  simpa [Function.comp_def] using h

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem wedge_swap_two_three
    (β : E [⋀^Fin 2]→L[ℝ] ℝ)
    (γ : E [⋀^Fin 3]→L[ℝ] ℝ) :
    wedge (ContinuousLinearMap.mul ℝ ℝ) β γ =
    wedge (ContinuousLinearMap.mul ℝ ℝ) γ β := by
  ext v
  have h := QuaternionicSymmetry.ContinuousWedgeGradedSwap.wedge_swap
    (p := 3) (q := 2) (by omega) (by omega) γ β v
  norm_num at h
  simpa [Function.comp_def] using h

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem wedge_triple_swap
    (α : E [⋀^Fin 1]→L[ℝ] ℝ)
    (β γ : E [⋀^Fin 2]→L[ℝ] ℝ) :
    wedge (ContinuousLinearMap.mul ℝ ℝ)
      (wedge (ContinuousLinearMap.mul ℝ ℝ) α β) γ =
    wedge (ContinuousLinearMap.mul ℝ ℝ)
      (wedge (ContinuousLinearMap.mul ℝ ℝ) α γ) β := by
  rw [wedge_assoc_one_two_two, wedge_swap_two_two β γ,
    ← wedge_assoc_one_two_two]

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem wedge_sum_skew_cancel
    (α : Fin 3 → Fin 3 → E [⋀^Fin 1]→L[ℝ] ℝ)
    (beta : Fin 3 → E [⋀^Fin 2]→L[ℝ] ℝ)
    (hskew : ∀ s t, α s t = -α t s) :
    (∑ t : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ)
      (∑ s : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ) (α s t) (beta s)) (beta t)) +
    (∑ t : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ) (beta t)
      (∑ s : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ) (α s t) (beta s))) = 0 := by
  let T (s t : Fin 3) : E [⋀^Fin 5]→L[ℝ] ℝ :=
    wedge (ContinuousLinearMap.mul ℝ ℝ)
      (wedge (ContinuousLinearMap.mul ℝ ℝ) (α s t) (beta s)) (beta t)
  have hterm (s t : Fin 3) : T s t = -T t s := by
    dsimp [T]
    rw [wedge_triple_swap]
    rw [hskew s t]
    have hneg (a : E [⋀^Fin 1]→L[ℝ] ℝ)
        (b : E [⋀^Fin 2]→L[ℝ] ℝ) :
        wedge (ContinuousLinearMap.mul ℝ ℝ) (-a) b =
          -wedge (ContinuousLinearMap.mul ℝ ℝ) a b := by
      simpa using wedge_smul_left (ContinuousLinearMap.mul ℝ ℝ) (-1 : ℝ) a b
    rw [hneg]
    simpa using wedge_smul_left (ContinuousLinearMap.mul ℝ ℝ) (-1 : ℝ)
      (wedge (ContinuousLinearMap.mul ℝ ℝ) (α t s) (beta t)) (beta s)
  have hfirst : (∑ t : Fin 3, ∑ s : Fin 3, T s t) = 0 := by
    have hpair : (∑ t : Fin 3, ∑ s : Fin 3, T s t) =
        -(∑ t : Fin 3, ∑ s : Fin 3, T s t) := by
      calc
        (∑ t : Fin 3, ∑ s : Fin 3, T s t) =
            ∑ s : Fin 3, ∑ t : Fin 3, T s t := Finset.sum_comm
        _ = ∑ s : Fin 3, ∑ t : Fin 3, -T t s := by
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro t _
          exact hterm s t
        _ = -(∑ t : Fin 3, ∑ s : Fin 3, T s t) := by
          simp only [Finset.sum_neg_distrib]
    ext v
    have hv := congrArg (fun f : E [⋀^Fin 5]→L[ℝ] ℝ => f v) hpair
    have hz : (∑ t : Fin 3, ∑ s : Fin 3, T s t) v = 0 := by
      change (∑ t : Fin 3, ∑ s : Fin 3, T s t) v =
        (- (∑ t : Fin 3, ∑ s : Fin 3, T s t)) v at hv
      simp only [ContinuousAlternatingMap.neg_apply] at hv
      linarith
    simpa using hz
  have hlin (t : Fin 3) :
      wedge (ContinuousLinearMap.mul ℝ ℝ)
          (∑ s : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ)
            (α s t) (beta s)) (beta t) = ∑ s : Fin 3, T s t := by
    simp [Fin.sum_univ_three, wedge_add_left, T]
  have hswap (t : Fin 3) :
      wedge (ContinuousLinearMap.mul ℝ ℝ) (beta t)
          (∑ s : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ)
            (α s t) (beta s)) =
      wedge (ContinuousLinearMap.mul ℝ ℝ)
          (∑ s : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ)
            (α s t) (beta s)) (beta t) :=
    wedge_swap_two_three _ _
  simp_rw [hswap, hlin]
  rw [hfirst]
  simp

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem fundamentalFourForm_closed (D : CompatibleTangentConnection Q) :
    QuaternionicSymmetry.ManifoldDifferentialForms.exteriorDerivative
      (fundamentalFourForm Q) = 0 := by
  apply (fourFormData Q).toForm_closed
  intro p y hy
  change extDeriv (fun z => ∑ t : Fin 3,
    wedge (ContinuousLinearMap.mul ℝ ℝ)
      (localKahlerField Q p t z) (localKahlerField Q p t z)) y = 0
  rw [QuaternionicSymmetry.LocalPolynomialTransgressionIntegral.extDeriv_finset_sum]
  · have hterm (t : Fin 3) :
        extDeriv (fun z => wedge (ContinuousLinearMap.mul ℝ ℝ)
          (localKahlerField Q p t z) (localKahlerField Q p t z)) y =
          wedge (ContinuousLinearMap.mul ℝ ℝ)
            (extDeriv (localKahlerField Q p t) y) (localKahlerField Q p t y) +
          wedge (ContinuousLinearMap.mul ℝ ℝ)
            (localKahlerField Q p t y) (extDeriv (localKahlerField Q p t) y) := by
        ext v
        have hdiff : DifferentiableAt ℝ (localKahlerField Q p t) y :=
          differentiableAt_chartKahler Q p y hy t
        have h := QuaternionicSymmetry.ContinuousWedgeLeibniz.extDeriv_wedge_apply
          (ContinuousLinearMap.mul ℝ ℝ)
          (localKahlerField Q p t) (localKahlerField Q p t) y hdiff hdiff v
        simpa [wedgeLeftIndex, Function.comp_def] using h
    simp_rw [hterm, extDeriv_localKahler Q D p y hy]
    let α : Fin 3 → Fin 3 → E [⋀^Fin 1]→L[ℝ] ℝ :=
      fun s t => inducedOneForm Q D p y s t
    let beta : Fin 3 → E [⋀^Fin 2]→L[ℝ] ℝ :=
      fun s => localKahlerField Q p s y
    have hskew (s t : Fin 3) : α s t = -α t s := by
      ext v
      have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A t s)
        (ManifoldQuaternionicFourFormConnection.inducedMatrix_skew Q D p y (v 0) hy)
      simpa [α, inducedOneForm_apply, Matrix.transpose_apply] using h
    have hcancel := wedge_sum_skew_cancel α beta hskew
    rw [Finset.sum_add_distrib]
    dsimp only [α, beta] at hcancel
    rw [hcancel]
  · intro t ht
    have hdiff : DifferentiableAt ℝ (localKahlerField Q p t) y :=
      differentiableAt_chartKahler Q p y hy t
    exact differentiableAt_wedge (ContinuousLinearMap.mul ℝ ℝ)
      (localKahlerField Q p t) (localKahlerField Q p t) y hdiff hdiff

end
end QuaternionicSymmetry.ManifoldQuaternionicFourFormClosed
