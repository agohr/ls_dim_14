import QuaternionicSymmetry.ManifoldTwistorHolomorphicAdditiveSheaf

/-! The actual complete linear system of a twistor contact-line twist.
Its base locus is the common zero locus of all genuine global holomorphic
coefficient sections. A finite basis cuts out precisely the same set.
This does not assume ampleness, projectivity, or a codimension estimate. -/
namespace QuaternionicSymmetry.ManifoldTwistorLinearSystem
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicMetric ManifoldQuaternionicConnection
open TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A) (r : ℤ)

abbrev GlobalSections :=
  coefficientSectionSubmodule Q D L r (⊤ : Opens (SphereBundleTotal Q))

/-- Evaluation takes values in the actual line-bundle fiber. -/
def evaluation (x : SphereBundleTotal Q) :
    GlobalSections Q D L r →ₗ[ℂ] (L.integerTwistCore Q D r).Fiber x where
  toFun s := s.1 ⟨x, Set.mem_univ x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def zeroSet (s : GlobalSections Q D L r) : Set (SphereBundleTotal Q) :=
  {x | evaluation Q D L r x s = 0}

def baseLocus : Set (SphereBundleTotal Q) :=
  {x | ∀ s : GlobalSections Q D L r, evaluation Q D L r x s = 0}

theorem baseLocus_subset_zeroSet (s : GlobalSections Q D L r) :
    baseLocus Q D L r ⊆ zeroSet Q D L r s := by
  intro x hx
  exact hx s

theorem baseLocus_eq_iInter_zeroSet :
    baseLocus Q D L r = ⋂ s : GlobalSections Q D L r, zeroSet Q D L r s := by
  ext x
  simp [baseLocus, zeroSet]

theorem mem_baseLocus_iff_basis {ι : Type*}
    (b : Module.Basis ι ℂ (GlobalSections Q D L r)) (x : SphereBundleTotal Q) :
    x ∈ baseLocus Q D L r ↔ ∀ i, evaluation Q D L r x (b i) = 0 := by
  constructor
  · intro h i
    exact h (b i)
  · intro h s
    have he : evaluation Q D L r x = 0 := by
      apply b.ext
      intro i
      exact h i
    rw [he]
    rfl

/-- In finite dimension, these are exactly the finitely many local equations
needed before a principal-ideal codimension theorem can be applied. -/
theorem baseLocus_eq_basis_zeroSets {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (GlobalSections Q D L r)) :
    baseLocus Q D L r = ⋂ i : ι, zeroSet Q D L r (b i) := by
  ext x
  simp only [Set.mem_iInter, zeroSet, Set.mem_setOf_eq]
  exact mem_baseLocus_iff_basis Q D L r b x

theorem section_eq_zero_iff (s : GlobalSections Q D L r) :
    s = 0 ↔ ∀ x : SphereBundleTotal Q, evaluation Q D L r x s = 0 := by
  constructor
  · intro h x
    rw [h, map_zero]
  · intro h
    apply Subtype.ext
    funext x
    exact h x.1

theorem exists_nonzero_value (s : GlobalSections Q D L r) (hs : s ≠ 0) :
    ∃ x : SphereBundleTotal Q, evaluation Q D L r x s ≠ 0 := by
  classical
  simpa only [not_forall] using
    (mt (section_eq_zero_iff Q D L r s).mpr hs)

theorem baseLocus_eq_univ_iff :
    baseLocus Q D L r = Set.univ ↔ ∀ s : GlobalSections Q D L r, s = 0 := by
  constructor
  · intro h s
    apply (section_eq_zero_iff Q D L r s).mpr
    intro x
    have hx : x ∈ baseLocus Q D L r := by rw [h]; trivial
    exact hx s
  · intro h
    apply Set.eq_univ_of_forall
    intro x s
    rw [h s, map_zero]

end
end QuaternionicSymmetry.ManifoldTwistorLinearSystem
