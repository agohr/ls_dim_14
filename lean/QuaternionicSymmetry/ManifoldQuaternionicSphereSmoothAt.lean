import QuaternionicSymmetry.ManifoldTwistorSphereSmoothTransition

/-! Local smoothness criterion for a sphere-valued map. Mathlib provides
the global version; the twistor isometry lift needs a pointwise version. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicSphereSmoothAt

open scoped Manifold ContDiff InnerProductSpace
noncomputable section

variable {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
  {m : WithTop ℕ∞} {n : ℕ}
  [Fact (Module.finrank ℝ E = n + 1)]

/-- A map into the Euclidean unit sphere is smooth at a point whenever its
ambient vector-valued map is smooth there. -/
theorem contMDiffAt_codRestrict_sphere
    {f : M → E} {x : M} (hf : ContMDiffAt I 𝓘(ℝ,E) m f x)
    (hf' : ∀ y, f y ∈ Metric.sphere (0 : E) 1) :
    ContMDiffAt I (𝓡 n) m
      (Set.codRestrict f (Metric.sphere (0 : E) 1) hf') x := by
  rw [contMDiffAt_iff_target]
  refine ⟨hf.continuousAt.codRestrict hf', ?_⟩
  let v : Metric.sphere (0 : E) 1 := ⟨f x, hf' x⟩
  let U : _ ≃ₗᵢ[ℝ] _ :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton
      n (ne_zero_of_mem_unit_sphere (-v))).repr
  have h : ContDiffOn ℝ ω U Set.univ := U.contDiff.contDiffOn
  have H₁ := (h.comp_inter contDiffOn_stereoToFun).contMDiffOn
  have hsource : f x ∈ {y : E | innerSL ℝ (-v : E) y ≠ (1 : ℝ)} := by
    change inner ℝ (-v : E) (f x) ≠ (1 : ℝ)
    have hv : ‖f x‖ = 1 := (mem_sphere_zero_iff_norm).mp (hf' x)
    simp [v, inner_neg_left, hv]
    norm_num
  have hopen : IsOpen {y : E | innerSL ℝ (-v : E) y ≠ (1 : ℝ)} :=
    isOpen_ne.preimage (innerSL ℝ (-v : E)).continuous
  have H₂ : ContMDiffOn 𝓘(ℝ,E) (𝓡 n) m
      (U ∘ stereoToFun (-v : E))
      ({y : E | innerSL ℝ (-v : E) y ≠ (1 : ℝ)} ∩
        stereoToFun (-v : E) ⁻¹' Set.univ) := H₁.of_le le_top
  have htarget := H₂.contMDiffAt
    (by simpa only [Set.preimage_univ, Set.inter_univ] using
      hopen.mem_nhds hsource)
  have hcomp := htarget.comp x hf
  convert hcomp using 1

end
end QuaternionicSymmetry.ManifoldQuaternionicSphereSmoothAt
