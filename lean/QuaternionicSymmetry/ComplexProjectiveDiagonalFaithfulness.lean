import QuaternionicSymmetry.ComplexProjectiveDiagonalKernelDetection

/-! A complex-torus action intertwined with a diagonal projective action
through an injective map is faithful if its compact restriction is faithful.
No separate faithfulness of complexification is a hypothesis. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalFaithfulness

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalKernelDetection TorusLaurentRepresentation
open ManifoldQuaternionicTorusAction
noncomputable section

theorem action_injective_of_compact {r d : ℕ} {X : Type*}
    (μ : Fin (d + 1) → Fin r → ℤ)
    (ρ : ComplexTorus r →* Equiv.Perm X)
    (ι : X → Space d) (hι : Function.Injective ι)
    (hProjective : ∀ z x, ι (ρ z x) = projectiveAction μ z (ι x))
    (hCompact : Function.Injective (fun t : Torus r => ρ (compactInclusion r t))) :
    Function.Injective ρ := by
  have hKernel (t : Torus r)
      (ht : ∀ x ∈ Set.range ι, projectiveAction μ (compactInclusion r t) x = x) :
      t = 1 := by
    apply hCompact
    apply Equiv.ext
    intro x
    apply hι
    calc
      ι (ρ (compactInclusion r t) x) =
          projectiveAction μ (compactInclusion r t) (ι x) := hProjective _ _
      _ = ι x := ht _ ⟨x, rfl⟩
      _ = ι (ρ (compactInclusion r 1) x) := by simp
  apply (injective_iff_map_eq_one ρ).mpr
  intro z hz
  apply complex_pointwise_kernel_trivial_of_compact μ (Set.range ι) hKernel z
  rintro _ ⟨x, rfl⟩
  rw [← hProjective, hz]
  rfl

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalFaithfulness
