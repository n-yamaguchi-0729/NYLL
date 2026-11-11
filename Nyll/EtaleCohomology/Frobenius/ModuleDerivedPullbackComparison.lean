/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CoefficientEndomorphism
public import Nyll.EtaleCohomology.Classical.DerivedGlobalSections
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.ModuleDerivedPullbackComparison
public import Nyll.EtaleCohomology.Classical.ModuleInjectiveResolution
public import Nyll.EtaleCohomology.Frobenius.BaseChangeSheafEquivalence
public import Nyll.EtaleCohomology.Frobenius.ExtensionByZeroCohomology
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Native-derived comparison for the original finite-field Frobenius

The actual base-changed extension-by-zero sheaf and its established coefficient
isomorphism instantiate the proved native-derived coefficient action. Every
power acts on the original classical cohomology through that same comparison.
-/

@[expose] public section

noncomputable section

universe u wX wR

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

section ActualFrobenius

variable (k : Type u) [Field k] [Fintype k] {U Z : Scheme.{u}}
  [U.Over (Spec (CommRingCat.of k))] [Z.Over (Spec (CommRingCat.of k))]
  (j : U ⟶ Z) [IsOpenImmersion j] (R' : Type u) [CommRing R']
  (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

local notation "JΩ" => etaleBaseChangeExtensionByZero k j R' Ω

variable
  [HasDerivedCategory.{wX} (Sheaf
    (pullback (Z ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).smallEtaleTopology (ModuleCat.{u} R'))]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R')]

/-- The original Frobenius and its original extension-by-zero coefficient
isomorphism act on the actual native derived global-section object. -/
def finiteFieldFrobeniusExtensionByZeroModuleDerived
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} R')) :
    End ((etaleModuleDerivedGlobalSections (pullback (Z ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) R').obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj ((JΩ).obj F))) :=
  etaleCoefficientModuleDerivedEndomorphism (R := R')
    (g := Scheme.constantBaseChangeFrobenius k Ω Z) ((JΩ).obj F)
    ((etaleBaseChangeExtensionByZeroFrobeniusCoefficientIso k j R' Ω).hom.app F)

/-- The actual native derived Frobenius induces the original classical
Frobenius on extension-by-zero cohomology in every degree. Preservation of
injectives is supplied by the proved Frobenius pullback equivalence. -/
theorem finiteFieldFrobeniusExtensionByZeroModuleDerived_cohomology
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} R')) (n : ℕ)
    (x : etaleCohomology (pullback (Z ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) R' ((JΩ).obj F) n) :
    etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv (pullback (Z ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) R' ((JΩ).obj F) n
        (finiteFieldFrobeniusExtensionByZeroCohomology k j R' Ω F n x) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R') (n : ℤ)).map
        (finiteFieldFrobeniusExtensionByZeroModuleDerived k j R' Ω F).asHom
        (etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv
          (pullback (Z ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) R' ((JΩ).obj F) n x) :=
  etaleCoefficientModuleDerivedEndomorphism_cohomology (R := R')
    (g := Scheme.constantBaseChangeFrobenius k Ω Z) ((JΩ).obj F)
    ((etaleBaseChangeExtensionByZeroFrobeniusCoefficientIso k j R' Ω).hom.app F) n x

/-- Every natural power, hence every positive Frobenius power in the trace
problem, has the same actual native-derived and classical action. -/
theorem finiteFieldFrobeniusExtensionByZeroModuleDerived_cohomology_pow
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} R')) (n m : ℕ)
    (x : etaleCohomology (pullback (Z ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) R' ((JΩ).obj F) n) :
    etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv (pullback (Z ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) R' ((JΩ).obj F) n
        (((finiteFieldFrobeniusExtensionByZeroCohomology k j R' Ω F n) ^ m) x) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R') (n : ℤ)).map
        ((finiteFieldFrobeniusExtensionByZeroModuleDerived k j R' Ω F) ^ m).asHom
        (etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv
          (pullback (Z ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) R' ((JΩ).obj F) n x) :=
  etaleCoefficientModuleDerivedEndomorphism_cohomology_pow (R := R')
    (g := Scheme.constantBaseChangeFrobenius k Ω Z) ((JΩ).obj F)
    ((etaleBaseChangeExtensionByZeroFrobeniusCoefficientIso k j R' Ω).hom.app F) n m x

end ActualFrobenius

end EtaleCohomology
