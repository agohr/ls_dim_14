import QuaternionicSymmetry.ManifoldTwistorHolomorphicAdditiveSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.LinearAlgebra.Dimension.Finite

set_option maxHeartbeats 120000
set_option synthInstance.maxHeartbeats 40000

/-! Derived sheaf cohomology of the actual holomorphic contact-line twists.
This defines the genuine groups `H^s(Z,L^r)` through Mathlib's Ext-based
sheaf cohomology, without assigning their dimensions or vanishing. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

universe u v w

open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

private def derivedSheafCohomology (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [Abelian (TopCat.Sheaf AddCommGrpCat.{v} X)]
    [hExt : HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{v} X)]
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (s : ℕ) : Type w :=
  @CategoryTheory.Abelian.Ext _ _ _ hExt
    ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))) F s

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

variable [HasSheafify (Opens.grothendieckTopology
    (TopCat.of (SphereBundleTotal Q))) AddCommGrpCat]
  [twistorAbelian : Abelian
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (SphereBundleTotal Q)))]
variable [twistorHasExt : HasExt.{w}
  (TopCat.Sheaf AddCommGrpCat (TopCat.of (SphereBundleTotal Q)))]

/-- Actual Ext-based cohomology of the holomorphic section sheaf of `L^r`. -/
abbrev holomorphicTwistCohomology {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (s : ℕ) :=
  letI := A.charts
  derivedSheafCohomology (TopCat.of (SphereBundleTotal Q))
    (holomorphicSectionAdditiveSheaf Q D L r) s

noncomputable instance holomorphicTwistCohomology_addCommGroup {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (s : ℕ) :
    AddCommGroup (holomorphicTwistCohomology Q D L r s) := by
  letI := A.charts
  unfold holomorphicTwistCohomology derivedSheafCohomology
  infer_instance

/-- Degree-zero derived cohomology is the morphism group from the constant
integer sheaf. This is the first, purely categorical, part of the usual
identification of `H⁰` with global holomorphic sections. -/
noncomputable def holomorphicTwistCohomologyZeroMorphismEquiv {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    holomorphicTwistCohomology Q D L r 0 ≃
      ((CategoryTheory.constantSheaf
          (Opens.grothendieckTopology (TopCat.of (SphereBundleTotal Q)))
          AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ)) ⟶
        holomorphicSectionAdditiveSheaf Q D L r) := by
  letI := A.charts
  exact (@CategoryTheory.Abelian.Ext.addEquiv₀
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (SphereBundleTotal Q)))
    inferInstance twistorAbelian twistorHasExt _ _).toEquiv

/-- Degree-zero derived cohomology is precisely the space of global
holomorphic coefficient sections of the actual integer twist. The section
space is evaluated on the top open of the twistor space. -/
noncomputable def holomorphicTwistCohomologyZeroEquiv {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    holomorphicTwistCohomology Q D L r 0 ≃
      (holomorphicSectionAdditiveSheaf Q D L r).presheaf.obj
        (Opposite.op (⊤ : Opens (TopCat.of (SphereBundleTotal Q)))) := by
  letI := A.charts
  let J := Opens.grothendieckTopology (TopCat.of (SphereBundleTotal Q))
  let F := holomorphicSectionAdditiveSheaf Q D L r
  exact (holomorphicTwistCohomologyZeroMorphismEquiv Q D L r).trans
    (((CategoryTheory.constantSheafAdj J AddCommGrpCat
        CategoryTheory.Limits.isTerminalTop).homEquiv _ _).trans
      (CategoryTheory.ConcreteCategory.homEquiv.trans
        (uliftZMultiplesHom _).symm))

/-- The target of the degree-zero comparison is the actual complex vector
space of global holomorphic coefficient sections, constructed chartwise. -/
noncomputable def holomorphicTwistCohomologyZeroVectorEquiv {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    holomorphicTwistCohomology Q D L r 0 ≃
      coefficientSectionSubmodule Q D L r
        (⊤ : Opens (TopCat.of (SphereBundleTotal Q))) := by
  letI := A.charts
  exact holomorphicTwistCohomologyZeroEquiv Q D L r

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

namespace QuaternionicSymmetry.FiniteSheafEuler

noncomputable section

/-! Finite Euler-characteristic algebra, applicable once complex module
structures and finite dimensionality have been established on the genuine
derived cohomology groups. It makes no assertion that these hypotheses hold
for the twistor sheaf. -/

variable (V : ℕ → Type*) [∀ s, AddCommGroup (V s)]
  [∀ s, Module ℂ (V s)]

/-- The finite alternating complex dimension of a cohomology family. -/
def eulerCharacteristic (topDegree : ℕ)
    (_hfinite : ∀ s, FiniteDimensional ℂ (V s)) : ℤ :=
  ∑ s ∈ Finset.range (topDegree + 1),
    (-1 : ℤ) ^ s * (Module.finrank ℂ (V s) : ℤ)

/-- If every positive-degree group up to the top degree vanishes, the
Euler characteristic is the dimension of global sections. -/
theorem eulerCharacteristic_eq_zeroDegree (topDegree : ℕ)
    (hfinite : ∀ s, FiniteDimensional ℂ (V s))
    (hvanish : ∀ s, 0 < s → s ≤ topDegree → Subsingleton (V s)) :
    eulerCharacteristic V topDegree hfinite =
      (Module.finrank ℂ (V 0) : ℤ) := by
  unfold eulerCharacteristic
  rw [Finset.sum_eq_single 0]
  · simp
  · intro s hs hs0
    have hspos : 0 < s := Nat.pos_of_ne_zero hs0
    have hle : s ≤ topDegree := by
      have := Finset.mem_range.mp hs
      omega
    letI := hvanish s hspos hle
    simp [Module.finrank_zero_of_subsingleton]
  · simp

/-- If all terms below the top degree vanish, only top cohomology
contributes to the finite Euler sum. -/
theorem eulerCharacteristic_eq_topDegree (topDegree : ℕ)
    (hfinite : ∀ s, FiniteDimensional ℂ (V s))
    (hvanish : ∀ s, s < topDegree → Subsingleton (V s)) :
    eulerCharacteristic V topDegree hfinite =
      (-1 : ℤ) ^ topDegree * (Module.finrank ℂ (V topDegree) : ℤ) := by
  unfold eulerCharacteristic
  rw [Finset.sum_eq_single topDegree]
  · intro s hs hsne
    have hslt : s < topDegree := by
      have hle : s ≤ topDegree := by
        have := Finset.mem_range.mp hs
        omega
      omega
    letI := hvanish s hslt
    simp [Module.finrank_zero_of_subsingleton]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _)))

end
end QuaternionicSymmetry.FiniteSheafEuler
