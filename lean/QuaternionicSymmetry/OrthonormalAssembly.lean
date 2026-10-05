import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-!
  Assembly of orthonormal families lying in orthogonal subspaces.

  This is a finite- or infinite-index linear-algebra statement over real inner
  product spaces; no quaternionic or spectral input is used here.
-/

namespace QuaternionicSymmetry
namespace OrthonormalAssembly

variable {V ι κ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Concatenate two vector families, with the two summands indexed by `Sum`. -/
def sumFamily (f : ι → V) (g : κ → V) : ι ⊕ κ → V
  | .inl i => f i
  | .inr j => g j

theorem orthonormal_sum (f : ι → V) (g : κ → V)
    (hf : Orthonormal ℝ f) (hg : Orthonormal ℝ g)
    (hfg : ∀ i j, inner ℝ (f i) (g j) = 0) :
    Orthonormal ℝ (sumFamily f g) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rcases a with i | j <;> rcases b with i' | j'
  · simpa only [sumFamily, Sum.inl.injEq] using (orthonormal_iff_ite.mp hf i i')
  · change inner ℝ (f i) (g j') = 0
    exact hfg i j'
  · change inner ℝ (g j) (f i') = 0
    rw [real_inner_comm]
    exact hfg i' j
  · simpa only [sumFamily, Sum.inr.injEq] using (orthonormal_iff_ite.mp hg j j')

theorem orthonormal_sum_of_subspaces (f : ι → V) (g : κ → V)
    (W U : Submodule ℝ V) (hf : Orthonormal ℝ f) (hg : Orthonormal ℝ g)
    (hfW : ∀ i, f i ∈ W) (hgU : ∀ j, g j ∈ U)
    (horth : ∀ x ∈ W, ∀ y ∈ U, inner ℝ x y = 0) :
    Orthonormal ℝ (sumFamily f g) :=
  orthonormal_sum f g hf hg fun i j => horth (f i) (hfW i) (g j) (hgU j)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
private theorem range_sumFamily (f : ι → V) (g : κ → V) :
    Set.range (sumFamily f g) = Set.range f ∪ Set.range g := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rcases a with i | j
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨j, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr j, rfl⟩

/-- The span of the concatenated family is the supremum of the two spans. -/
theorem span_sumFamily (f : ι → V) (g : κ → V) :
    Submodule.span ℝ (Set.range (sumFamily f g)) =
      Submodule.span ℝ (Set.range f) ⊔ Submodule.span ℝ (Set.range g) := by
  rw [range_sumFamily, Submodule.span_union]

/-- If the two families span subspaces whose supremum is all of `V`, their concatenation spans
the whole space. -/
theorem span_sumFamily_eq_top (f : ι → V) (g : κ → V) (W U : Submodule ℝ V)
    (hf : Submodule.span ℝ (Set.range f) = W)
    (hg : Submodule.span ℝ (Set.range g) = U) (hWU : W ⊔ U = ⊤) :
    Submodule.span ℝ (Set.range (sumFamily f g)) = ⊤ := by
  rw [span_sumFamily, hf, hg, hWU]

/-- In finite dimension a subspace and its orthogonal complement span the whole space. -/
theorem sup_orthogonal_eq_top [FiniteDimensional ℝ V] (W : Submodule ℝ V) :
    W ⊔ W.orthogonal = ⊤ :=
  Submodule.sup_orthogonal_of_hasOrthogonalProjection

end OrthonormalAssembly
end QuaternionicSymmetry
