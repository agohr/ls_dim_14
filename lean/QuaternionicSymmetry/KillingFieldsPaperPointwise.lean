import QuaternionicSymmetry.KillingFieldsPaperMatrixPadding
import QuaternionicSymmetry.KillingFieldsPaperWeights
import QuaternionicSymmetry.QuaternionicE14OrbitalSums

/-! Fixed-rank orbital positivity on every ambient quaternionic dimension
through fourteen. Matrix rank and manifold dimension are separate parameters. -/
namespace QuaternionicSymmetry.KillingFieldsPaperPointwise
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
open MatrixTracePolynomial QuaternionicE14OrbitalPointwise
open KillingFieldsPaperMatrixPadding KillingFieldsPaperCertificate
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {ι β V : Type*} [Fintype ι] [Fintype β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Padding leaves every positive signed trace generator unchanged. -/
theorem sevenValues_pad {n N : ℕ} (hn : n ≤ N)
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (s : ℝ)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (η : β → E V) :
    sevenValues Q b s (fun i => pad hn (A i)) η = sevenValues Q b s A η := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [sevenValues, Fin.cases_succ]
    rw [signedTracePower_pad hn A η (i.val+1) (by omega)]

theorem orbital_term_in_positive_ray
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (n k : ℕ) (hn : n ≤ 14) (hk : k ≤ 6) (hkn : k ≤ n)
    (j : Fin 12)
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (s : ℝ) (hs : 0 ≤ s)
    (hqdim : Q.quaternionicDimension = n)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : ∀ i, QuaternionicMatrixModel.HermitianAntiSelfDual (A i))
    (η : β → E V) (hη : ∀ i, η i ∈ HyperholomorphicExterior.formSpace Q b) :
    PositiveRay.Contains (embed (V := V) (topForm Q b))
      (aeval (sevenValues Q b s A η)
        (DimensionThirteenFourteenDensity.u ^ (n-k) * moment k j)) := by
  rw [← sevenValues_pad hn Q b s A η, moment]
  rw [map_mul, map_pow, DimensionThirteenFourteenDensity.u, aeval_X,
    eval_embed_forms]
  change PositiveRay.Contains _ ((s • embed (V := V) (form Q b)) ^ (n-k) * _)
  rw [smul_pow, smul_mul_assoc]
  apply PositiveRay.smul ?_ (pow_nonneg hs _)
  obtain ⟨r, hr, he⟩ := OrbitalPointwisePolynomialSign.orbital_mem_positiveRay
    hsource 14 k (by omega) hk (profile j) (profiles_admissible j).1
    (fun i => pad hn (A i)) (fun i => pad_hermitianAntiSelfDual hn (A i) (hA i))
    Q b η hη (by omega)
  refine ⟨r, hr, ?_⟩
  have hm := congrArg (embed (V := V)) he
  rw [map_mul, map_pow, hqdim] at hm
  rw [mul_comm]
  exact hm.trans ((embed (V := V)).toLinearMap.map_smul r (topForm Q b))

theorem remainder_nonnegative
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14)
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (s : ℝ) (hs : 0 ≤ s)
    (hqdim : Q.quaternionicDimension = n)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : ∀ i, QuaternionicMatrixModel.HermitianAntiSelfDual (A i))
    (η : β → E V) (hη : ∀ i, η i ∈ HyperholomorphicExterior.formSpace Q b)
    (F : CE V →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := V) (topForm Q b))) :
    0 ≤ F (aeval (sevenValues Q b s A η) (remainder n)) := by
  let L := QuaternionicE14OrbitalSums.evaluatedFunctional (sevenValues Q b s A η) F
  change 0 ≤ L _
  unfold remainder
  rw [map_list_sum]
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
  rw [← smul_eq_C_mul, map_smul, Rat.smul_def]
  obtain ⟨hc, _, hk, hkn⟩ := terms_admissible n hn t ht
  apply mul_nonneg (by exact_mod_cast hc.le)
  exact PositiveRay.functional_nonneg
    (orbital_term_in_positive_ray hsource n t.2.1 hn.2 hk hkn t.2.2
      Q b s hs hqdim A hA η hη) F hF

end
end QuaternionicSymmetry.KillingFieldsPaperPointwise
