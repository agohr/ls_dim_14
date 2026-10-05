import QuaternionicSymmetry.ManifoldDeRhamRing
import QuaternionicSymmetry.ContinuousWedgeUnit

/-!
The zero-degree de Rham piece and the constant-one tangent zero-form.
Exact forms in degree zero are the zero subspace.
-/

namespace QuaternionicSymmetry.ManifoldDeRhamDegreeZero

open QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldDeRhamWedge
  QuaternionicSymmetry.ManifoldDeRhamRing
open scoped Manifold ContDiff Topology

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private noncomputable instance tangentNormedGroup (x : M) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := by
  change NormedAddCommGroup E
  infer_instance

private noncomputable instance tangentNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := by
  change NormedSpace ℝ E
  infer_instance

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem castForm_apply_alt {m n : ℕ} (h : m = n)
    (α : Form 𝓘(ℝ, E) M m) (x : M) :
    castForm h α x = ContinuousWedgeUnit.castAlt h (α x) := by
  cases h
  rfl

/-- Degree-zero cohomology is the space of smooth closed zero-forms. -/
noncomputable abbrev zeroDegreeCohomology :=
  closedForms (E := E) (M₀ := M) 0

/-- There is no incoming exterior derivative in degree zero. -/
noncomputable def exactZeroSubmodule :
    Submodule ℝ (zeroDegreeCohomology (E := E) (M := M)) := ⊥

/-- The constant-one form on the genuine tangent zero-fibers. -/
noncomputable def oneForm : Form 𝓘(ℝ, E) M 0 :=
  fun x => ContinuousWedgeUnit.oneZero (E := TangentSpace 𝓘(ℝ, E) x)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem inChartModel_oneForm (x : M) :
    inChartModel x (oneForm (E := E) (M := M)) =
      fun _ : E => ContinuousWedgeUnit.oneZero (E := E) := by
  ext y v
  simp [inChartModel_apply, oneForm, ContinuousWedgeUnit.oneZero]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem oneForm_smooth : ChartSmooth (oneForm (E := E) (M := M)) := by
  intro x
  rw [inChartModel_oneForm]
  exact contDiffOn_const

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem oneForm_closed :
    exteriorDerivative (oneForm (E := E) (M := M)) = 0 := by
  funext x
  change ContinuousAlternatingMap.compContinuousLinearMap
    (extDeriv (inChartModel x (oneForm (E := E) (M := M)))
      (extChartAt 𝓘(ℝ, E) x x))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x) = 0
  rw [inChartModel_oneForm]
  have hz : extDeriv
      (fun _ : E => ContinuousWedgeUnit.oneZero (E := E))
      (extChartAt 𝓘(ℝ, E) x x) = 0 := by
    ext v
    simp [ContinuousWedgeUnit.oneZero, extDeriv_constOfIsEmpty]
  rw [hz]
  ext v
  rfl

/-- The unit in degree-zero cohomology. -/
noncomputable def oneClass : zeroDegreeCohomology (E := E) (M := M) :=
  ⟨⟨oneForm, oneForm_smooth⟩, by
    change smoothExteriorDerivative (E := E) (M₀ := M) 0
      ⟨oneForm, oneForm_smooth⟩ = 0
    apply Subtype.ext
    exact oneForm_closed⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formWedge_one_right {n : ℕ}
    (α : Form 𝓘(ℝ, E) M n) :
    formWedge α (oneForm (E := E) (M := M)) = α := by
  funext x
  exact ContinuousWedgeUnit.wedge_one_right (α x)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formWedge_one_left {n : ℕ}
    (α : Form 𝓘(ℝ, E) M n) :
    castForm (Nat.zero_add n)
      (formWedge (oneForm (E := E) (M := M)) α) = α := by
  have h : formWedge (oneForm (E := E) (M := M)) α =
      castForm (Nat.zero_add n).symm α := by
    funext x
    ext v
    change (ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousWedgeUnit.oneZero (E := TangentSpace 𝓘(ℝ, E) x))
      (α x)) v = (castForm (Nat.zero_add n).symm α x) v
    rw [ContinuousWedgeUnit.wedge_one_left]
    rw [castForm_apply_alt]
  rw [h, castForm_comp]
  rfl

end QuaternionicSymmetry.ManifoldDeRhamDegreeZero
