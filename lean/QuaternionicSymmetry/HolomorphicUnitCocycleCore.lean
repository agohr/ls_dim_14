import QuaternionicSymmetry.HolomorphicLineUnitCocycle

/-! Reconstruct a genuine holomorphic line-bundle core from an arbitrary
Čech one-cocycle of the actual holomorphic-unit sheaf on an open cover.
The supplied data are just the cover and its cocycle, not a bundle or an
assumed realization theorem. Comparison with derived H¹ is separate. -/

namespace QuaternionicSymmetry.HolomorphicUnitCocycleCore

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicUnitSheaf
open HolomorphicLinePowers HolomorphicLineUnitCocycle SheafCechOneCocycle
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H) {U : ι → Opens B}
  (c : OneCocycle (unitSheaf (B := B) IB) U)

abbrev cocycleUnit (i j : ι) (V : Opens B)
    (hi : V ≤ U i) (hj : V ≤ U j) : (Functions IB V)ˣ :=
  (c.value i j V hi hj).toMul

def scalar (i j : ι) (x : B) : ℂ := by
  classical
  exact if hx : x ∈ U i ⊓ U j then
    (cocycleUnit IB c i j (U i ⊓ U j) inf_le_left inf_le_right).val ⟨x, hx⟩
  else 0

theorem scalar_of_mem (i j : ι) (x : B) (hx : x ∈ U i ⊓ U j) :
    scalar IB c i j x =
      (cocycleUnit IB c i j (U i ⊓ U j) inf_le_left inf_le_right).val ⟨x, hx⟩ :=
  dif_pos hx

theorem scalar_holomorphic (i j : ι) :
    ContMDiffOn IB 𝓘(ℂ, ℂ) ∞ (scalar IB c i j) (U i ∩ U j) := by
  have h : ContMDiff IB 𝓘(ℂ, ℂ) ∞
      (fun x : (U i ⊓ U j : Opens B) => scalar IB c i j x.1) := by
    convert (cocycleUnit IB c i j (U i ⊓ U j)
      inf_le_left inf_le_right).val.contMDiff using 1
    funext x
    exact scalar_of_mem IB c i j x.1 x.2
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (h ⟨x, hx⟩)).contMDiffWithinAt

theorem scalar_eq_value (i j : ι) (V : Opens B)
    (hi : V ≤ U i) (hj : V ≤ U j) (x : V) :
    scalar IB c i j x.1 = (cocycleUnit IB c i j V hi hj).val x := by
  rw [scalar_of_mem IB c i j x.1 ⟨hi x.2, hj x.2⟩]
  exact congrArg (fun s : Additive (Functions IB V)ˣ => s.toMul.val x)
    (c.naturality i j (U i ⊓ U j) V (le_inf hi hj) inf_le_left inf_le_right)

theorem scalar_self (i : ι) (x : B) (hx : x ∈ U i) :
    scalar IB c i i x = 1 := by
  rw [scalar_eq_value IB c i i (U i) le_rfl le_rfl ⟨x, hx⟩]
  exact congrArg (fun s : Additive (Functions IB (U i))ˣ => s.toMul.val ⟨x, hx⟩)
    (c.self i (U i) le_rfl)

theorem scalar_comp (i j k : ι) (x : B) (hx : x ∈ (U i ⊓ U j) ⊓ U k) :
    scalar IB c j k x * scalar IB c i j x = scalar IB c i k x := by
  let V := (U i ⊓ U j) ⊓ U k
  have hi : V ≤ U i := inf_le_left.trans inf_le_left
  have hj : V ≤ U j := inf_le_left.trans inf_le_right
  have hk : V ≤ U k := inf_le_right
  let xx : V := ⟨x, hx⟩
  rw [scalar_eq_value IB c j k V hj hk xx,
    scalar_eq_value IB c i j V hi hj xx, scalar_eq_value IB c i k V hi hk xx]
  have h := congrArg (fun s : Additive (Functions IB V)ˣ => s.toMul.val xx)
    (c.cocycle i j k V hi hj hk)
  change (cocycleUnit IB c i j V hi hj).val xx *
    (cocycleUnit IB c j k V hj hk).val xx =
    (cocycleUnit IB c i k V hi hk).val xx at h
  simpa only [mul_comm] using h

variable (indexAt : B → ι) (mem_at : ∀ x : B, x ∈ U (indexAt x))

/-- Actual scalar coordinate changes, with their smoothness and cocycle
proved from the holomorphic-unit sheaf data. -/
def lineCore : VectorBundleCore ℂ B ℂ ι where
  baseSet i := U i
  isOpen_baseSet i := (U i).isOpen
  indexAt := indexAt
  mem_baseSet_at := mem_at
  coordChange i j x := scalar IB c i j x • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by
    rw [scalar_self IB c i x hx]
    simp
  continuousOn_coordChange i j :=
    (scalar_holomorphic IB c i j).continuousOn.smul continuousOn_const
  coordChange_comp i j k x hx v := by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← mul_assoc, scalar_comp IB c i j k x hx]

instance lineCore_isContMDiff : (lineCore IB c indexAt mem_at).IsContMDiff IB ∞ where
  contMDiffOn_coordChange i j :=
    (scalar_holomorphic IB c i j).smul contMDiffOn_const

theorem lineCore_transitionScalar (i j : ι) (x : B) :
    transitionScalar (lineCore IB c indexAt mem_at) i j x = scalar IB c i j x := by
  simp [transitionScalar, lineCore]

/-- Reconstructing the line core recovers the original cocycle section on
every smaller overlap, not merely its values at the chosen cover points. -/
theorem unitCocycle_lineCore_value (i j : ι) (V : Opens B)
    (hi : V ≤ U i) (hj : V ≤ U j) :
    (unitCocycle IB (lineCore IB c indexAt mem_at)).value i j V hi hj =
      c.value i j V hi hj := by
  apply Units.ext
  apply Subtype.ext
  funext x
  change transitionScalar (lineCore IB c indexAt mem_at) i j x.1 =
    (cocycleUnit IB c i j V hi hj).val x
  rw [lineCore_transitionScalar]
  exact scalar_eq_value IB c i j V hi hj x

end
end QuaternionicSymmetry.HolomorphicUnitCocycleCore
