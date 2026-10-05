import QuaternionicSymmetry.TorusFaithfulWeightSpan

/-! A faithful family of actual integral compact-torus characters has
real-spanning weight functionals. The coordinate exponential proof is
internal and does not assume a weight-span theorem or a smooth Lie atlas. -/

namespace QuaternionicSymmetry.TorusFaithfulCharacterWeightSpan

open TorusFaithfulWeightSpan
open ManifoldQuaternionicTorusAction
open SelectedTorusCompactExponentialSmooth
open scoped BigOperators
noncomputable section

variable {r : ℕ}

theorem weightCharacter_circleExpPi (μ : Fin r → ℤ) (u : Fin r → ℝ) :
    weightCharacter μ (circleExpPi r u) =
      Circle.exp (integralWeightLinear μ u) := by
  classical
  change (∏ i : Fin r, (Circle.exp (u i)) ^ μ i) =
    Circle.exp (∑ i : Fin r, (μ i : ℝ) * u i)
  suffices h : ∀ s : Finset (Fin r),
      (∏ i ∈ s, (Circle.exp (u i)) ^ μ i) =
        Circle.exp (∑ i ∈ s, (μ i : ℝ) * u i) by
    simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        ← Circle.exp_intCast_mul, Circle.exp_add]

theorem integralWeight_span_top_of_faithful_characters {ι : Type*}
    (μ : ι → Fin r → ℤ)
    (hFaith : ∀ t : Torus r,
      (∀ j : ι, weightCharacter (μ j) t = 1) → t = 1) :
    Submodule.span ℝ (Set.range
      (fun j => integralWeightLinear (μ j))) = ⊤ := by
  apply integralWeight_span_top_of_common_kernel_zero μ
  intro u hu
  have hExpZero (t : ℝ) : circleExpPi r (t • u) = 1 := by
    apply hFaith
    intro j
    rw [weightCharacter_circleExpPi, map_smul, hu j]
    simp
  funext i
  by_contra hi
  let t : ℝ := Real.pi / u i
  have h := congrFun (hExpZero t) i
  change Circle.exp (t * u i) = 1 at h
  rw [show t * u i = Real.pi from div_mul_cancel₀ _ hi] at h
  exact Circle.exp_pi_ne_one h

end
end QuaternionicSymmetry.TorusFaithfulCharacterWeightSpan
