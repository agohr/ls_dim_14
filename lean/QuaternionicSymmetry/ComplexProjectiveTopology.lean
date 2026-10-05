import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Separation.Basic

/-! The canonical quotient topology and coordinate-nonzero domains of
finite-dimensional complex projective space. -/

namespace QuaternionicSymmetry.ComplexProjectiveTopology

open TopologicalSpace
open scoped Topology
open scoped LinearAlgebra.Projectivization

abbrev Coord (d : ℕ) := Fin (d + 1) → ℂ
abbrev Space (d : ℕ) := ℙ ℂ (Coord d)

/- The same quotient topology applies to the actual dual section space, not
just to a chosen coordinate model. -/
noncomputable instance (V : Type*) [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] : TopologicalSpace (ℙ ℂ V) :=
  TopologicalSpace.coinduced (Projectivization.mk' ℂ) inferInstance

/-- This is exactly the quotient topology of nonzero coordinate vectors
under nonzero complex rescaling. -/
theorem continuous_mk (d : ℕ) :
    Continuous (fun v : {v : Coord d // v ≠ 0} => Projectivization.mk' ℂ v) := by
  exact continuous_quotient_mk'

/-- The standard affine projective domain where coordinate `i` is nonzero. -/
def affineDomain (d : ℕ) (i : Fin (d + 1)) : Set (Space d) :=
  {p | p.rep i ≠ 0}

theorem mem_affineDomain_mk (d : ℕ) (i : Fin (d + 1))
    (v : Coord d) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ affineDomain d i ↔ v i ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  have hi := congrFun ha i
  change (Projectivization.mk ℂ v hv).rep i ≠ 0 ↔ v i ≠ 0
  rw [← hi]
  simp [Units.smul_def, smul_eq_mul]

/-- Each coordinate-nonzero domain is open in the genuine quotient
topology, not declared open by fiat. -/
theorem isOpen_affineDomain (d : ℕ) (i : Fin (d + 1)) :
    IsOpen (affineDomain d i) := by
  change IsOpen[TopologicalSpace.coinduced (Projectivization.mk' ℂ) inferInstance]
    (affineDomain d i)
  apply isOpen_coinduced.mpr
  have hpre : (Projectivization.mk' ℂ : {v : Coord d // v ≠ 0} → Space d) ⁻¹'
      affineDomain d i = {v | v.1 i ≠ 0} := by
    ext v
    exact mem_affineDomain_mk d i v.1 v.2
  rw [hpre]
  exact isOpen_ne.preimage ((continuous_apply i).comp continuous_subtype_val)

/-- The finitely many standard affine coordinate domains cover the entire
projectivization, because a projective representative is nonzero. -/
theorem exists_mem_affineDomain (d : ℕ) (p : Space d) :
    ∃ i : Fin (d + 1), p ∈ affineDomain d i := by
  by_contra h
  have hz : p.rep = 0 := by
    funext i
    have hi : ¬p ∈ affineDomain d i := by
      intro hp
      exact h ⟨i, hp⟩
    by_contra hne
    exact hi hne
  exact p.rep_nonzero hz

end QuaternionicSymmetry.ComplexProjectiveTopology
