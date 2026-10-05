import QuaternionicSymmetry.VectorBundleFrameTransitions
import QuaternionicSymmetry.QuaternionicRangeFrameCoordinates

/-! Quaternionic spans can be detected through an injective intertwining
map. This supplies the overlap and projected-connection algebra. -/
namespace QuaternionicSymmetry.QuaternionicFrameInjectionSpan
open VectorBundleFrameTransitions
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (S : QuaternionicStructure F) (Q : QuaternionicStructure E) (B : F →L[ℝ] E)
  (hI : ∀ v, B (S.I v) = Q.I (B v)) (hJ : ∀ v, B (S.J v) = Q.J (B v))

include hI hJ in
theorem generator_intertwines (t : Fin 3) (v : F) :
    B (quaternionicGenerator S t v) = quaternionicGenerator Q t (B v) := by
  fin_cases t
  · exact hI v
  · exact hJ v
  · change B (S.I (S.J v)) = Q.I (Q.J (B v))
    rw [hI,hJ]

include hI hJ in
theorem mem_span_iff (hB : Function.Injective B) (T : F →L[ℝ] F) :
    T ∈ quaternionicSpan S ↔ ∃ A ∈ quaternionicSpan Q, ∀ v, B (T v) = A (B v) := by
  classical
  constructor
  · intro hT
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hT
    refine ⟨∑ t, a t • quaternionicGenerator Q t,
      Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (generator_mem_span Q t)),?_⟩
    intro v
    rw [← ha]
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,map_sum,map_smul,
      generator_intertwines S Q B hI hJ]
  · rintro ⟨A,hA,hAB⟩
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hA
    have hT : T = ∑ t, a t • quaternionicGenerator S t := by
      ext v
      apply hB
      rw [hAB,← ha]
      simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,map_sum,map_smul,
        generator_intertwines S Q B hI hJ]
    rw [hT]
    exact Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (generator_mem_span S t))

end
end QuaternionicSymmetry.QuaternionicFrameInjectionSpan
