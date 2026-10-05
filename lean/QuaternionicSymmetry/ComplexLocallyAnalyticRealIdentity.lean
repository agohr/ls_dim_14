import QuaternionicSymmetry.ComplexLocallyAnalyticZeroSet

/-! Holomorphic uniqueness from the real axes, including the finite-product
version needed to extend compact-torus identities through exponential
parameters.  These are statements about genuine locally analytic zero sets,
not Zariski density assumptions. -/

namespace QuaternionicSymmetry.ComplexLocallyAnalyticZeroSet

open Set Filter
open scoped Topology

/-- A locally analytic zero set containing the real axis is all of `ℂ`. -/
theorem eq_univ_of_real {S : Set ℂ} (hS : LocallyAnalyticZeroSet S)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ S) : S = univ := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact eq_univ_of_frequently hS
    (ht.frequently (Filter.Eventually.of_forall hreal).frequently)

/-- If every complex coordinate slice has a locally analytic zero set,
vanishing on all real coordinate tuples forces vanishing everywhere.
Separate local defining functions are allowed on each slice. -/
theorem eq_univ_of_real_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set (ι → ℂ)}
    (hslice : ∀ (z : ι → ℂ) (i : ι),
      LocallyAnalyticZeroSet {w : ℂ | Function.update z i w ∈ S})
    (hreal : ∀ t : ι → ℝ, (fun i => (t i : ℂ)) ∈ S) : S = univ := by
  have hfinite : ∀ a : Finset ι, ∀ z : ι → ℂ,
      (∀ i, i ∉ a → (z i).im = 0) → z ∈ S := by
    intro a
    induction a using Finset.induction_on with
    | empty =>
        intro z hz
        have heq : (fun i => ((z i).re : ℂ)) = z := by
          funext i
          apply Complex.ext <;> simp [hz i (by simp)]
        exact heq ▸ hreal (fun i => (z i).re)
    | @insert i a hi ih =>
        intro z hz
        have hline : ∀ t : ℝ, Function.update z i (t : ℂ) ∈ S := by
          intro t
          apply ih
          intro j hj
          by_cases hji : j = i
          · subst j
            simp
          · simp only [Function.update_of_ne hji]
            exact hz j (by simp [hji, hj])
        have hall := eq_univ_of_real (hslice z i) hline
        have hzi : Function.update z i (z i) ∈ S := by
          exact show z i ∈ {w : ℂ | Function.update z i w ∈ S} from
            hall ▸ Set.mem_univ (z i)
        simpa using hzi
  apply Set.eq_univ_of_forall
  intro z
  exact hfinite Finset.univ z (by simp)

end QuaternionicSymmetry.ComplexLocallyAnalyticZeroSet
