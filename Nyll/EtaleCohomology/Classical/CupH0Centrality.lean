/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.CupTensorSheaves
public import Nyll.EtaleCohomology.Classical.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Original degree-zero cup acts centrally on arbitrary schemes

An endomorphism of the original regular constant sheaf acts naturally
on every original module sheaf through the actual tensor unit. The
component at that same unit recovers the original endomorphism.
Naturality of the original Ext groups therefore identifies degree-zero
cup with the induced coefficient action and proves centrality.

No connectedness assumption or comparison of H⁰ with constant scalars
is needed. No positive-degree graded commutativity is asserted.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Abelian MonoidalCategory
open scoped EtaleCohomology.ModuleTensor

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

private theorem unitEndomorphism_conjugate
    {C : Type*} [Category* C] [MonoidalCategory C] (s : 𝟙_ C ⟶ 𝟙_ C) :
    (λ_ (𝟙_ C)).inv ≫ (s ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom = s := by
  rw [unitors_inv_equal, unitors_equal]
  exact (whiskerRight_id_symm s).symm

private theorem ext_identity_naturality
    {C : Type*} [Category* C] [Abelian C] [HasExt.{u} C]
    {A B : C} {n : ℕ} (a : Ext.{u} A B n) (t : 𝟭 C ⟶ 𝟭 C) :
    a.comp (Ext.mk₀ (t.app B)) (add_zero n) =
      (Ext.mk₀ (t.app A)).comp a (zero_add n) := by
  simpa only [Ext.id_mapExactFunctor] using
    (Ext.mapExactFunctor_comp_mk₀_natTransApp a (F := 𝟭 C) (G := 𝟭 C) t)

/-- A regular-unit endomorphism acts on every module sheaf through the left unitor. -/
def regularUnitEndomorphismAction
    (s : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R) ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) :
    𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ⟶
      𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  (leftUnitorNatIso (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).inv ≫
    (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).map s ≫
      (leftUnitorNatIso (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).hom

private theorem regularUnitEndomorphismAction_constant
    (s : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R) ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) :
    (regularUnitEndomorphismAction X R s).app
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) = s := by
  change (λ_ (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))).inv ≫
      (s ▷ (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))) ≫
      (λ_ (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))).hom = s
  exact unitEndomorphism_conjugate
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) s

/-- Every original H⁰ class defines its actual natural coefficient
endomorphism on all original module sheaves. -/
def etaleCohomologyH0CoefficientAction
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 0) :
    𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ⟶
      𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  regularUnitEndomorphismAction X R
    (Ext.homEquiv₀ ((etaleConstantModuleExtCohomologyEquiv X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 0).symm x))

/-- On the original regular coefficients, the natural H⁰ action
recovers the original degree-zero Ext class. -/
theorem etaleCohomologyH0CoefficientAction_constant
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 0) :
    Ext.mk₀ ((etaleCohomologyH0CoefficientAction X R x).app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))) =
      (etaleConstantModuleExtCohomologyEquiv X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        0).symm x := by
  rw [etaleCohomologyH0CoefficientAction, regularUnitEndomorphismAction_constant,
    Ext.mk₀_homEquiv₀_apply]

/-- On any original coefficient sheaf, cup by an original H⁰ class
is the cohomology map of its actual natural coefficient endomorphism. -/
theorem etaleCohomologyCup_zero_eq_coefficientMap
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 0)
    (y : etaleCohomology X R F n) :
    etaleCohomologyCup X R F 0 n n (zero_add n) x y =
      Classical.cohomologyMap ((etaleCohomologyH0CoefficientAction X R x).app F) n y := by
  let U := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let e := etaleConstantModuleExtCohomologyEquiv X R F n
  let α := (etaleConstantModuleExtCohomologyEquiv X R U 0).symm x
  let β := e.symm y
  let t := etaleCohomologyH0CoefficientAction X R x
  have ht : Ext.mk₀ (t.app U) = α := etaleCohomologyH0CoefficientAction_constant X R x
  have hnat : β.comp (Ext.mk₀ (t.app F)) (add_zero n) =
      (Ext.mk₀ (t.app U)).comp β (zero_add n) :=
    ext_identity_naturality (A := U) (B := F) β t
  have hcomm : β.comp (Ext.mk₀ (t.app F)) (add_zero n) = α.comp β (zero_add n) :=
    hnat.trans (congrArg (fun z : Ext.{u} U U 0 => z.comp β (zero_add n)) ht)
  have hcup : etaleCohomologyCup X R F 0 n n (zero_add n) x y =
      e (α.comp β (zero_add n)) := etaleCohomologyCup_apply X R F 0 n n (zero_add n) x y
  have hswap : e (α.comp β (zero_add n)) =
      e (β.comp (Ext.mk₀ (t.app F)) (add_zero n)) := congrArg e hcomm.symm
  have hmap : e (β.comp (Ext.mk₀ (t.app F)) (add_zero n)) =
      Classical.cohomologyMap (t.app F) n (e β) :=
    etaleConstantModuleExtCohomologyEquiv_naturality X R (t.app F) n β
  have hy : Classical.cohomologyMap (t.app F) n (e β) =
      Classical.cohomologyMap (t.app F) n y :=
    congrArg (fun z : etaleCohomology X R F n => Classical.cohomologyMap (t.app F) n z)
      (e.apply_symm_apply y)
  exact hcup.trans (hswap.trans (hmap.trans hy))

/-- Original degree-zero constant-coefficient classes commute with
all original constant-coefficient cup classes on every scheme. -/
theorem etaleCohomologyCup_comm_zero_left (n : ℕ)
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 0)
    (y : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) n) :
    etaleCohomologyCup X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        0 n n (zero_add n) x y =
      etaleCohomologyCup X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        n 0 n (add_zero n) y x := by
  let U := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let e := etaleConstantModuleExtCohomologyEquiv X R U n
  let α := (etaleConstantModuleExtCohomologyEquiv X R U 0).symm x
  let β := e.symm y
  let t := etaleCohomologyH0CoefficientAction X R x
  have ht : Ext.mk₀ (t.app U) = α := etaleCohomologyH0CoefficientAction_constant X R x
  have hnat : β.comp (Ext.mk₀ (t.app U)) (add_zero n) =
      (Ext.mk₀ (t.app U)).comp β (zero_add n) :=
    ext_identity_naturality (A := U) (B := U) β t
  have hl : β.comp α (add_zero n) =
      β.comp (Ext.mk₀ (t.app U)) (add_zero n) :=
    congrArg (fun z : Ext.{u} U U 0 => β.comp z (add_zero n)) ht.symm
  have hr : (Ext.mk₀ (t.app U)).comp β (zero_add n) = α.comp β (zero_add n) :=
    congrArg (fun z : Ext.{u} U U 0 => z.comp β (zero_add n)) ht
  have hcomm : β.comp α (add_zero n) = α.comp β (zero_add n) :=
    hl.trans (hnat.trans hr)
  rw [etaleCohomologyCup_apply, etaleCohomologyCup_apply]
  exact congrArg e hcomm.symm

end EtaleCohomology
