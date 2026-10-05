import QuaternionicSymmetry.FourDimensionalDegree
import QuaternionicSymmetry.EvenForms

/-! Quaternionic four-coordinate blocks in an exterior algebra. -/

namespace QuaternionicSymmetry.QuaternionicBlocks

open scoped BigOperators

noncomputable section

variable {β : Type*} [DecidableEq β]

/-- A finite direct sum of four-dimensional real coordinate blocks. -/
abbrev V (β : Type*) := β × Fin 4 → ℝ

abbrev E (β : Type*) := ExteriorAlgebra ℝ (V β)

/-- The inclusion of the `j`th four-dimensional coordinate block. -/
def insert (j : β) : FourDimensionalForms.V →ₗ[ℝ] V β where
  toFun x := fun p ↦ if p.1 = j then x p.2 else 0
  map_add' x y := by
    ext p
    by_cases h : p.1 = j <;> simp [h]
  map_smul' r x := by
    ext p
    by_cases h : p.1 = j <;> simp [h]

def g (j : β) (k : Fin 4) : E β :=
  ExteriorAlgebra.ι ℝ (insert j (FourDimensionalForms.e k))

/-- The anti-self-dual two-form in the `j`th coordinate block. -/
def α (j : β) : E β :=
  ExteriorAlgebra.map (insert j) FourDimensionalForms.α

def ωI (j : β) : E β :=
  ExteriorAlgebra.map (insert j) FourDimensionalForms.ωI

def ωJ (j : β) : E β :=
  ExteriorAlgebra.map (insert j) FourDimensionalForms.ωJ

def ωK (j : β) : E β :=
  ExteriorAlgebra.map (insert j) FourDimensionalForms.ωK

def vol (j : β) : E β :=
  ExteriorAlgebra.map (insert j) FourDimensionalForms.vol

theorem alpha_eq (j : β) :
    α j = g j 0 * g j 1 - g j 2 * g j 3 := by
  simp [α, g, FourDimensionalForms.α, FourDimensionalForms.g]

theorem omegaI_eq (j : β) :
    ωI j = g j 0 * g j 1 + g j 2 * g j 3 := by
  simp [ωI, g, FourDimensionalForms.ωI, FourDimensionalForms.g]

theorem omegaJ_eq (j : β) :
    ωJ j = g j 0 * g j 2 - g j 1 * g j 3 := by
  simp [ωJ, g, FourDimensionalForms.ωJ, FourDimensionalForms.g]

theorem omegaK_eq (j : β) :
    ωK j = g j 0 * g j 3 + g j 1 * g j 2 := by
  simp [ωK, g, FourDimensionalForms.ωK, FourDimensionalForms.g]

theorem vol_eq (j : β) :
    vol j = g j 0 * g j 1 * g j 2 * g j 3 := by
  simp [vol, g, FourDimensionalForms.vol, FourDimensionalForms.g]

theorem alpha_sq (j : β) : α j ^ 2 = -(2 : ℝ) • vol j := by
  simpa only [α, vol, map_pow, map_neg, map_smul] using
    congrArg (ExteriorAlgebra.map (insert j)) FourDimensionalForms.alpha_sq

theorem omega_sum_sq (j : β) :
    ωI j ^ 2 + ωJ j ^ 2 + ωK j ^ 2 = (6 : ℝ) • vol j := by
  simpa only [ωI, ωJ, ωK, vol, map_pow, map_add, map_smul] using
    congrArg (ExteriorAlgebra.map (insert j)) FourDimensionalForms.omega_sum_sq

private theorem g_degree_one (j : β) (k : Fin 4) :
    g j k ∈ ExteriorAlgebra.exteriorPower ℝ 1 (V β) := by
  change g j k ∈ (LinearMap.range (ExteriorAlgebra.ι ℝ : V β →ₗ[ℝ] E β)) ^ 1
  simpa only [pow_one] using
    LinearMap.mem_range_self (ExteriorAlgebra.ι ℝ : V β →ₗ[ℝ] E β)
      (insert j (FourDimensionalForms.e k))

private theorem pair_degree_two (j : β) (a b : Fin 4) :
    g j a * g j b ∈ ExteriorAlgebra.exteriorPower ℝ 2 (V β) := by
  simpa only [one_add_one_eq_two] using
    SetLike.mul_mem_graded (g_degree_one j a) (g_degree_one j b)

theorem alpha_degree (j : β) : α j ∈ ExteriorAlgebra.exteriorPower ℝ 2 (V β) := by
  rw [alpha_eq]
  exact (ExteriorAlgebra.exteriorPower ℝ 2 (V β)).sub_mem
    (pair_degree_two j 0 1) (pair_degree_two j 2 3)

theorem omegaI_degree (j : β) : ωI j ∈ ExteriorAlgebra.exteriorPower ℝ 2 (V β) := by
  rw [omegaI_eq]
  exact (ExteriorAlgebra.exteriorPower ℝ 2 (V β)).add_mem
    (pair_degree_two j 0 1) (pair_degree_two j 2 3)

theorem omegaJ_degree (j : β) : ωJ j ∈ ExteriorAlgebra.exteriorPower ℝ 2 (V β) := by
  rw [omegaJ_eq]
  exact (ExteriorAlgebra.exteriorPower ℝ 2 (V β)).sub_mem
    (pair_degree_two j 0 2) (pair_degree_two j 1 3)

theorem omegaK_degree (j : β) : ωK j ∈ ExteriorAlgebra.exteriorPower ℝ 2 (V β) := by
  rw [omegaK_eq]
  exact (ExteriorAlgebra.exteriorPower ℝ 2 (V β)).add_mem
    (pair_degree_two j 0 3) (pair_degree_two j 1 2)

theorem vol_degree (j : β) : vol j ∈ ExteriorAlgebra.exteriorPower ℝ 4 (V β) := by
  rw [vol_eq]
  simpa only [mul_assoc, two_add_two_eq_four] using
    SetLike.mul_mem_graded (pair_degree_two j 0 1) (pair_degree_two j 2 3)

theorem alpha_cube (j : β) : α j ^ 3 = 0 := by
  simpa only [α, map_pow, map_zero] using
    congrArg (ExteriorAlgebra.map (insert j)) FourDimensionalForms.alpha_cube

theorem vol_sq (j : β) : vol j ^ 2 = 0 := by
  simpa only [vol, map_pow, map_zero] using
    congrArg (ExteriorAlgebra.map (insert j)) FourDimensionalForms.vol_sq

private theorem pair_even (j : β) (a b : Fin 4) :
    g j a * g j b ∈ EvenForms.evenSubalgebra ℝ (V β) :=
  EvenForms.pair_mem _ _

theorem alpha_even (j : β) : α j ∈ EvenForms.evenSubalgebra ℝ (V β) := by
  rw [alpha_eq]
  exact (EvenForms.evenSubalgebra ℝ (V β)).sub_mem (pair_even j 0 1) (pair_even j 2 3)

theorem omegaI_even (j : β) : ωI j ∈ EvenForms.evenSubalgebra ℝ (V β) := by
  rw [omegaI_eq]
  exact (EvenForms.evenSubalgebra ℝ (V β)).add_mem (pair_even j 0 1) (pair_even j 2 3)

theorem omegaJ_even (j : β) : ωJ j ∈ EvenForms.evenSubalgebra ℝ (V β) := by
  rw [omegaJ_eq]
  exact (EvenForms.evenSubalgebra ℝ (V β)).sub_mem (pair_even j 0 2) (pair_even j 1 3)

theorem omegaK_even (j : β) : ωK j ∈ EvenForms.evenSubalgebra ℝ (V β) := by
  rw [omegaK_eq]
  exact (EvenForms.evenSubalgebra ℝ (V β)).add_mem (pair_even j 0 3) (pair_even j 1 2)

theorem vol_even (j : β) : vol j ∈ EvenForms.evenSubalgebra ℝ (V β) := by
  rw [vol_eq]
  simpa only [mul_assoc] using
    (EvenForms.evenSubalgebra ℝ (V β)).mul_mem (pair_even j 0 1) (pair_even j 2 3)

omit [DecidableEq β] in
theorem commute_of_even {x y : E β}
    (hx : x ∈ EvenForms.evenSubalgebra ℝ (V β))
    (hy : y ∈ EvenForms.evenSubalgebra ℝ (V β)) :
    Commute x y := by
  change x * y = y * x
  exact congrArg Subtype.val (mul_comm
    (⟨x, hx⟩ : EvenForms.evenSubalgebra ℝ (V β))
    (⟨y, hy⟩ : EvenForms.evenSubalgebra ℝ (V β)))

end
end QuaternionicSymmetry.QuaternionicBlocks
