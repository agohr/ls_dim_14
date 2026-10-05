import QuaternionicSymmetry.ComplexProjectiveAffineEuclidean
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Rational transition maps for the standard affine charts of complex projective space. -/

namespace QuaternionicSymmetry.ComplexProjectiveTopology

open scoped Topology ContDiff

/-- A Euclidean affine chart point lies in the overlap with the `j`-chart exactly
when its reconstructed `j`-th homogeneous coordinate is nonzero. -/
def euclideanOverlap (d : ℕ) (i j : Fin (d + 1)) : Set (Fin d → ℂ) :=
  {w | Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ) i (1 : ℂ) w j ≠ 0}

private theorem differentiable_insertNth_coordinate (d : ℕ)
    (i j : Fin (d + 1)) :
    Differentiable ℂ (fun w : Fin d → ℂ =>
      Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ) i (1 : ℂ) w j) := by
  by_cases hij : j = i
  · subst j
    simp
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    rw [← hk]
    simpa [Fin.insertNth_apply_succAbove] using (differentiable_apply k :
      Differentiable ℂ (fun w : Fin d → ℂ => w k))

private theorem contDiff_insertNth_coordinate (d : ℕ)
    (i j : Fin (d + 1)) :
    ContDiff ℂ ∞ (fun w : Fin d → ℂ =>
      Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ) i (1 : ℂ) w j) := by
  by_cases hij : j = i
  · subst j
    simpa using (contDiff_const : ContDiff ℂ ∞ (fun _ : Fin d → ℂ => (1 : ℂ)))
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    rw [← hk]
    simpa [Fin.insertNth_apply_succAbove] using
      (contDiff_apply ℂ ℂ k : ContDiff ℂ ∞ (fun w : Fin d → ℂ => w k))

theorem isOpen_euclideanOverlap (d : ℕ) (i j : Fin (d + 1)) :
    IsOpen (euclideanOverlap d i j) := by
  exact isOpen_ne.preimage (differentiable_insertNth_coordinate d i j).continuous

/-- The transition from the `i` Euclidean chart to the `j` Euclidean chart,
expressed by homogeneous-coordinate ratios. The formula is total as a function;
its holomorphic domain is `euclideanOverlap`. -/
noncomputable def euclideanTransition (d : ℕ) (i j : Fin (d + 1))
    (w : Fin d → ℂ) : Fin d → ℂ :=
  fun k => Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ) i (1 : ℂ) w (j.succAbove k) /
    Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ) i (1 : ℂ) w j

/-- Standard projective affine transition functions are holomorphic on
their genuine nonzero-denominator overlap. -/
theorem differentiableOn_euclideanTransition (d : ℕ)
    (i j : Fin (d + 1)) :
    DifferentiableOn ℂ (euclideanTransition d i j) (euclideanOverlap d i j) := by
  apply differentiableOn_pi.mpr
  intro k w hw
  change DifferentiableWithinAt ℂ
    (fun z : Fin d → ℂ =>
      Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ) i (1 : ℂ) z (j.succAbove k) /
      Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ) i (1 : ℂ) z j)
    (euclideanOverlap d i j) w
  have hnum : DifferentiableWithinAt ℂ
      (fun z : Fin d → ℂ =>
        Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ) i (1 : ℂ) z (j.succAbove k))
      (euclideanOverlap d i j) w :=
    ((differentiable_insertNth_coordinate d i (j.succAbove k)) w).differentiableWithinAt
  have hden : DifferentiableWithinAt ℂ
      (fun z : Fin d → ℂ =>
        Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ) i (1 : ℂ) z j)
      (euclideanOverlap d i j) w :=
    ((differentiable_insertNth_coordinate d i j) w).differentiableWithinAt
  have hnonzero : Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ)
      i (1 : ℂ) w j ≠ 0 := hw
  convert hnum.mul (hden.inv hnonzero) using 1

theorem contDiffOn_euclideanTransition (d : ℕ)
    (i j : Fin (d + 1)) :
    ContDiffOn ℂ ∞ (euclideanTransition d i j) (euclideanOverlap d i j) := by
  apply contDiffOn_pi.mpr
  intro k
  have hnum := (contDiff_insertNth_coordinate d i (j.succAbove k)).contDiffOn
    (s := euclideanOverlap d i j)
  have hden := (contDiff_insertNth_coordinate d i j).contDiffOn
    (s := euclideanOverlap d i j)
  have hnonzero : ∀ w ∈ euclideanOverlap d i j,
      Fin.insertNth (α := fun _ : Fin (d + 1) => ℂ) i (1 : ℂ) w j ≠ 0 :=
    fun _ hw => hw
  convert hnum.mul (hden.inv hnonzero) using 1

/-- The homogeneous vector reconstructed from Euclidean chart coordinates. -/
def homogeneousVector (d : ℕ) (i : Fin (d + 1))
    (w : Fin d → ℂ) : Coord d :=
  Fin.insertNth i 1 w

theorem homogeneousVector_i (d : ℕ) (i : Fin (d + 1))
    (w : Fin d → ℂ) : homogeneousVector d i w i = 1 := by
  simp [homogeneousVector]

theorem homogeneousVector_ne_zero (d : ℕ) (i : Fin (d + 1))
    (w : Fin d → ℂ) : homogeneousVector d i w ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [homogeneousVector_i] at hi

/-- Reconstruct the actual projective point from Euclidean chart coordinates. -/
noncomputable def euclideanPoint (d : ℕ) (i : Fin (d + 1))
    (w : Fin d → ℂ) : Space d :=
  Projectivization.mk ℂ (homogeneousVector d i w)
    (homogeneousVector_ne_zero d i w)

theorem euclideanPoint_mem_i (d : ℕ) (i : Fin (d + 1))
    (w : Fin d → ℂ) : euclideanPoint d i w ∈ affineDomain d i := by
  exact (mem_affineDomain_mk d i _ _).2
    (homogeneousVector_i d i w ▸ one_ne_zero)

theorem euclideanPoint_eq_chartInv (d : ℕ) (i : Fin (d + 1))
    (w : Fin d → ℂ) :
    euclideanPoint d i w = ((affineEuclideanHomeomorph d i).symm w).1 := by
  rfl

theorem euclideanPoint_mem_j_iff (d : ℕ) (i j : Fin (d + 1))
    (w : Fin d → ℂ) :
    euclideanPoint d i w ∈ affineDomain d j ↔ w ∈ euclideanOverlap d i j := by
  exact mem_affineDomain_mk d j (homogeneousVector d i w)
    (homogeneousVector_ne_zero d i w)

/-- The rational formula is precisely the transition obtained by applying the
actual `j`-chart to the projective point represented in the `i`-chart. -/
theorem euclideanTransition_eq_chart (d : ℕ) (i j : Fin (d + 1))
    (w : Fin d → ℂ) (hw : w ∈ euclideanOverlap d i j) :
    euclideanTransition d i j w =
      affineEuclideanHomeomorph d j
        ⟨euclideanPoint d i w, (euclideanPoint_mem_j_iff d i j w).2 hw⟩ := by
  funext k
  exact (affineRatio_mk d j (j.succAbove k)
    (homogeneousVector d i w) (homogeneousVector_ne_zero d i w) hw).symm

end QuaternionicSymmetry.ComplexProjectiveTopology
