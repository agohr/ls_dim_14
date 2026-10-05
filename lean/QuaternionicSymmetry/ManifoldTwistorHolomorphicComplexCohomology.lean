import QuaternionicSymmetry.ManifoldTwistorHolomorphicAdditiveSheaf
import QuaternionicSymmetry.ManifoldTwistorSectionComparison
import QuaternionicSymmetry.ManifoldTwistorZeroTwistSections
import QuaternionicSymmetry.ManifoldTwistorHolomorphicSheafCohomology
import QuaternionicSymmetry.SheafComplexLinear
import Mathlib.Algebra.Module.ULift

/-! Complex-linear Ext cohomology of the actual holomorphic integer contact
twists. The constant source is the rank-one complex module; sheaf Ext thus
represents derived global sections in the complex-module category. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open QuaternionicSymmetry.SheafComplexLinear
open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

universe u v w


private def derivedComplexSheafCohomology (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{v} ℂ)]
    [Abelian (TopCat.Sheaf (ModuleCat.{v} ℂ) X)]
    [hExt : HasExt.{w} (TopCat.Sheaf (ModuleCat.{v} ℂ) X)]
    (F : TopCat.Sheaf (ModuleCat.{v} ℂ) X) (s : ℕ) : Type w :=
  @CategoryTheory.Abelian.Ext _ _ _ hExt
    ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      (ModuleCat.{v} ℂ)).obj (ModuleCat.of ℂ (ULift.{v} ℂ))) F s

variable {E : Type u} {M : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

variable [HasSheafify (Opens.grothendieckTopology
    (TopCat.of (SphereBundleTotal Q))) (ModuleCat.{v} ℂ)]
  [twistorHasExt : HasExt.{w} (TopCat.Sheaf (ModuleCat.{v} ℂ)
    (TopCat.of (SphereBundleTotal Q)))]

example : Linear ℂ (TopCat.Sheaf (ModuleCat.{v} ℂ)
    (TopCat.of (SphereBundleTotal Q))) := inferInstance

/-- Actual complex-linear derived cohomology `H^s(Z,L^r)`, using the
complex-module sheaf of chartwise holomorphic contact-line sections. -/
abbrev holomorphicTwistComplexCohomology {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (s : ℕ) :=
  letI := A.charts
  derivedComplexSheafCohomology (TopCat.of (SphereBundleTotal Q))
    (holomorphicSectionComplexSheaf Q D L r) s

noncomputable instance holomorphicTwistComplexCohomology_addCommGroup {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (s : ℕ) :
    AddCommGroup (holomorphicTwistComplexCohomology Q D L r s) := by
  letI := A.charts
  exact @CategoryTheory.Abelian.Ext.instAddCommGroup
    (TopCat.Sheaf (ModuleCat.{v} ℂ) (TopCat.of (SphereBundleTotal Q)))
    inferInstance inferInstance twistorHasExt _ _ _

noncomputable instance holomorphicTwistComplexCohomology_module {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (s : ℕ) :
    Module ℂ (holomorphicTwistComplexCohomology Q D L r s) := by
  letI := A.charts
  unfold holomorphicTwistComplexCohomology derivedComplexSheafCohomology
  infer_instance

/-- The degree-zero part of complex-linear derived cohomology is the
morphism space from the constant rank-one sheaf. Its linearity is inherited
from Mathlib's `Ext.linearEquiv₀`; the wrapper equivalence records the
underlying functions without choosing a second hom-module instance. -/
noncomputable def holomorphicTwistComplexCohomologyZeroMorphismEquiv {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    holomorphicTwistComplexCohomology Q D L r 0 ≃
      ((CategoryTheory.constantSheaf
          (Opens.grothendieckTopology (TopCat.of (SphereBundleTotal Q)))
          (ModuleCat.{v} ℂ)).obj (ModuleCat.of ℂ (ULift.{v} ℂ)) ⟶
        holomorphicSectionComplexSheaf Q D L r) := by
  letI := A.charts
  let C := TopCat.Sheaf (ModuleCat.{v} ℂ) (TopCat.of (SphereBundleTotal Q))
  letI : Abelian C := inferInstance
  letI : Preadditive C := inferInstance
  have hLin : @Linear ℂ Complex.instSemiring C inferInstance inferInstance :=
    SheafComplexLinear.topCatSheafLinear (TopCat.of (SphereBundleTotal Q))
  exact (@CategoryTheory.Abelian.Ext.linearEquiv₀ ℂ inferInstance C inferInstance
    inferInstance hLin twistorHasExt _ _).toEquiv

/-- Canonical complex-linear refinement of the degree-zero Ext-to-Hom
comparison, using Mathlib's canonical Abelian structure on module sheaves. -/
noncomputable def holomorphicTwistComplexCohomologyZeroMorphismLinearEquiv {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    holomorphicTwistComplexCohomology Q D L r 0 ≃ₗ[ℂ]
      ((CategoryTheory.constantSheaf
          (Opens.grothendieckTopology (TopCat.of (SphereBundleTotal Q)))
          (ModuleCat.{v} ℂ)).obj (ModuleCat.of ℂ (ULift.{v} ℂ)) ⟶
        holomorphicSectionComplexSheaf Q D L r) := by
  letI := A.charts
  let C := TopCat.Sheaf (ModuleCat.{v} ℂ) (TopCat.of (SphereBundleTotal Q))
  exact @CategoryTheory.Abelian.Ext.linearEquiv₀ ℂ inferInstance C inferInstance
    inferInstance inferInstance twistorHasExt _ _

noncomputable instance constantTwistorSheaf_additive :
    (CategoryTheory.constantSheaf
      (Opens.grothendieckTopology (TopCat.of (SphereBundleTotal Q)))
      (ModuleCat.{v} ℂ)).Additive := by
  let J := Opens.grothendieckTopology (TopCat.of (SphereBundleTotal Q))
  letI : ((CategoryTheory.sheafSections J (ModuleCat.{v} ℂ)).obj
      (Opposite.op (⊤ : Opens (TopCat.of (SphereBundleTotal Q))))).Additive :=
    ⟨by intro X Y f g; rfl⟩
  exact (CategoryTheory.constantSheafAdj J (ModuleCat.{v} ℂ)
    CategoryTheory.Limits.isTerminalTop).left_adjoint_additive

noncomputable def constantTwistorSheafHomLinearEquiv {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    (((CategoryTheory.constantSheaf
        (Opens.grothendieckTopology (TopCat.of (SphereBundleTotal Q)))
        (ModuleCat.{v} ℂ)).obj (ModuleCat.of ℂ (ULift.{v} ℂ))) ⟶
      holomorphicSectionComplexSheaf Q D L r) ≃ₗ[ℂ]
      ((ModuleCat.of ℂ (ULift.{v} ℂ)) ⟶
        (holomorphicSectionComplexSheaf Q D L r).presheaf.obj
          (Opposite.op (⊤ : Opens (TopCat.of (SphereBundleTotal Q))))) := by
  letI := A.charts
  let J := Opens.grothendieckTopology (TopCat.of (SphereBundleTotal Q))
  exact SheafComplexLinear.adjunctionHomLinearEquiv
    (CategoryTheory.constantSheafAdj J (ModuleCat.{v} ℂ)
      CategoryTheory.Limits.isTerminalTop)
    (ModuleCat.of ℂ (ULift.{v} ℂ)) (holomorphicSectionComplexSheaf Q D L r)

/-- The natural degree-zero comparison with the actual holomorphic
coefficient sections on the whole twistor space. -/
noncomputable def holomorphicTwistComplexCohomologyZeroSectionEquiv {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    holomorphicTwistComplexCohomology Q D L r 0 ≃
      coefficientSectionSubmodule Q D L r
        (⊤ : Opens (TopCat.of (SphereBundleTotal Q))) := by
  letI := A.charts
  let J := Opens.grothendieckTopology (TopCat.of (SphereBundleTotal Q))
  let F := holomorphicSectionComplexSheaf Q D L r
  exact (holomorphicTwistComplexCohomologyZeroMorphismEquiv Q D L r).trans
    (((CategoryTheory.constantSheafAdj J (ModuleCat.{v} ℂ)
      CategoryTheory.Limits.isTerminalTop).homEquiv _ _).trans
      ((ModuleCat.homEquiv).trans
        (((LinearEquiv.arrowCongr (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ)
          (LinearEquiv.refl ℂ _)).toEquiv).trans
          (LinearMap.ringLmapEquivSelf ℂ ℂ _).toEquiv)))

/-- The canonical degree-zero comparison is complex linear, not merely
a bijection of underlying sections. -/
noncomputable def holomorphicTwistComplexCohomologyZeroSectionLinearEquiv {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    holomorphicTwistComplexCohomology Q D L r 0 ≃ₗ[ℂ]
      coefficientSectionSubmodule Q D L r
        (⊤ : Opens (TopCat.of (SphereBundleTotal Q))) := by
  letI := A.charts
  let F := holomorphicSectionComplexSheaf Q D L r
  exact ((holomorphicTwistComplexCohomologyZeroMorphismLinearEquiv Q D L r).trans
    (constantTwistorSheafHomLinearEquiv Q D L r)).trans
    ((SheafComplexLinear.moduleCatHomLinearEquiv
        (ModuleCat.of ℂ (ULift.{v} ℂ))
        (F.presheaf.obj
          (Opposite.op (⊤ : Opens (TopCat.of (SphereBundleTotal Q)))))).trans
      ((LinearEquiv.arrowCongr (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ)
        (LinearEquiv.refl ℂ _)).trans
        (LinearMap.ringLmapEquivSelf ℂ ℂ _)))

/-- The degree-zero derived group and bundled holomorphic sections have a
canonical bijection. Its complex-linearity is established separately from
this equivalence of underlying types. -/
noncomputable def holomorphicTwistComplexCohomologyZeroBundledEquiv {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    holomorphicTwistComplexCohomology Q D L r 0 ≃
      HolomorphicTwistSections Q D L r := by
  exact (holomorphicTwistComplexCohomologyZeroSectionEquiv Q D L r).trans
    (globalCoefficientSectionsEquiv Q D L r).toEquiv

/-- The derived `H⁰` group is naturally ℂ-linearly identified with
bundled holomorphic sections of the actual integer contact twist. -/
noncomputable def holomorphicTwistComplexCohomologyZeroBundledLinearEquiv {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    holomorphicTwistComplexCohomology Q D L r 0 ≃ₗ[ℂ]
      HolomorphicTwistSections Q D L r := by
  exact (holomorphicTwistComplexCohomologyZeroSectionLinearEquiv Q D L r).trans
    (globalCoefficientSectionsEquiv Q D L r)

/-- Consequently the actual derived `H⁰` and genuine holomorphic
section space have equal complex dimension, whenever either is finite. -/
theorem holomorphicTwistComplexCohomologyZero_finrank_eq {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    Module.finrank ℂ (holomorphicTwistComplexCohomology Q D L r 0) =
      Module.finrank ℂ (HolomorphicTwistSections Q D L r) :=
  (holomorphicTwistComplexCohomologyZeroBundledLinearEquiv Q D L r).finrank_eq

/-- The zero twist has one-dimensional derived `H⁰`, proved through
the actual compact connected twistor geometry and constant sections. -/
theorem holomorphicTwistComplexCohomologyZeroTwist_finrank {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    [CompactSpace M] [PreconnectedSpace M]
    (x : SphereBundleTotal Q) :
    Module.finrank ℂ (holomorphicTwistComplexCohomology Q D L 0 0) = 1 := by
  rw [(holomorphicTwistComplexCohomologyZeroSectionLinearEquiv Q D L 0).finrank_eq]
  exact zeroTwistSections_finrank Q D L x

noncomputable instance holomorphicTwistComplexCohomologyZeroTwist_finiteDimensional
    {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n A)
    [CompactSpace M] [PreconnectedSpace M] [Nonempty M] :
    FiniteDimensional ℂ (holomorphicTwistComplexCohomology Q D L 0 0) :=
  (holomorphicTwistComplexCohomologyZeroSectionLinearEquiv Q D L 0).symm.finiteDimensional

/-- The finite alternating sum attached to the actual complex-linear
twistor sheaf cohomology groups, conditional on finite dimensionality. -/
def holomorphicTwistComplexEulerCharacteristic {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (topDegree : ℕ)
    (hfinite : ∀ s, FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology Q D L r s)) : ℤ :=
  QuaternionicSymmetry.FiniteSheafEuler.eulerCharacteristic
    (holomorphicTwistComplexCohomology Q D L r) topDegree hfinite

/-- Positive-degree vanishing reduces the genuine derived Euler sum to
the complex dimension of degree-zero sheaf cohomology. -/
theorem holomorphicTwistComplexEulerCharacteristic_eq_zeroDegree {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (topDegree : ℕ)
    (hfinite : ∀ s, FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology Q D L r s))
    (hvanish : ∀ s, 0 < s → s ≤ topDegree →
      Subsingleton (holomorphicTwistComplexCohomology Q D L r s)) :
    holomorphicTwistComplexEulerCharacteristic Q D L r topDegree hfinite =
      (Module.finrank ℂ
        (holomorphicTwistComplexCohomology Q D L r 0) : ℤ) := by
  exact QuaternionicSymmetry.FiniteSheafEuler.eulerCharacteristic_eq_zeroDegree
    (holomorphicTwistComplexCohomology Q D L r) topDegree hfinite hvanish

/-- If the higher groups of the actual trivial twist vanish in the
complex-dimensional range, its Euler characteristic is one. The higher
vanishing remains an explicit geometric/source premise; the `H⁰` value is
proved internally from constant holomorphic sections. -/
theorem holomorphicTwistComplexEulerCharacteristic_zeroTwist {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    [CompactSpace M] [PreconnectedSpace M]
    (x : SphereBundleTotal Q)
    (hfinite : ∀ s, FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology Q D L 0 s))
    (hvanish : ∀ s, 0 < s → s ≤ 2 * n + 1 →
      Subsingleton (holomorphicTwistComplexCohomology Q D L 0 s)) :
    holomorphicTwistComplexEulerCharacteristic Q D L 0 (2 * n + 1) hfinite = 1 := by
  rw [holomorphicTwistComplexEulerCharacteristic_eq_zeroDegree Q D L 0
    (2 * n + 1) hfinite hvanish,
    holomorphicTwistComplexCohomologyZeroTwist_finrank Q D L x]
  norm_num

/-- In the positive/Fano twistor setting, source-relative higher
cohomology vanishing identifies the Hilbert value with the dimension of
actual holomorphic sections. This theorem does not assume that value. -/
theorem holomorphicTwistComplexEulerCharacteristic_nonnegativeTwist {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (_hr : 0 ≤ r)
    (hfinite : ∀ s, FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology Q D L r s))
    (hKodaira : ∀ s, 0 < s → s ≤ 2 * n + 1 →
      Subsingleton (holomorphicTwistComplexCohomology Q D L r s)) :
    holomorphicTwistComplexEulerCharacteristic Q D L r (2 * n + 1) hfinite =
      (Module.finrank ℂ (HolomorphicTwistSections Q D L r) : ℤ) := by
  rw [holomorphicTwistComplexEulerCharacteristic_eq_zeroDegree Q D L r
    (2 * n + 1) hfinite hKodaira,
    holomorphicTwistComplexCohomologyZero_finrank_eq Q D L r]

/-- In complex dimension `2n+1`, the negative-twist Kodaira vanishing
range in Semmelmann--Weingart, Section 2, removes every term below top
degree. The vanishing statement itself is an explicit source premise. -/
theorem holomorphicTwistComplexEulerCharacteristic_negativeTwist {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (_hr : r < 0)
    (hfinite : ∀ s, FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology Q D L r s))
    (hKodaira : ∀ s, s ≤ 2 * n →
      Subsingleton (holomorphicTwistComplexCohomology Q D L r s)) :
    holomorphicTwistComplexEulerCharacteristic Q D L r (2 * n + 1) hfinite =
      (-1 : ℤ) ^ (2 * n + 1) *
        (Module.finrank ℂ
          (holomorphicTwistComplexCohomology Q D L r (2 * n + 1)) : ℤ) := by
  exact QuaternionicSymmetry.FiniteSheafEuler.eulerCharacteristic_eq_topDegree
    (holomorphicTwistComplexCohomology Q D L r) (2 * n + 1) hfinite
    (by intro s hs; exact hKodaira s (by omega))

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
