/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Pi1.GaloisCategories.TrivialMonodromy
public import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso
public import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberFunctorComparison
public import Nyll.EtaleFundamentalGroups.GaloisCategories.Surjectivity

/-!
# Fibre change in the same trivial-monodromy category

The full subcategory is fixed using one original fibre functor. Any other
fibre functor restricts to that same category. Restricting an actual natural
isomorphism gives a continuous change-of-fibre isomorphism, compatible with
the original automorphism restrictions. Full faithfulness of the inclusion
makes the restriction at every fibre functor surjective.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] (F : C ⥤ FintypeCat.{w})
  (N : Subgroup (Aut F))

/-- Restriction at any finite-set-valued functor on the original category. -/
def trivialMonodromyRestrictionAt (F' : C ⥤ FintypeCat.{w}) :
    Aut F' →ₜ* Aut (trivialMonodromyInclusion F N ⋙ F') :=
  autHomOfCompIso (trivialMonodromyInclusion F N) (Iso.refl _)

/-- Restriction keeps the original automorphism on every retained fibre. -/
@[simp] theorem trivialMonodromyRestrictionAt_apply
    (F' : C ⥤ FintypeCat.{w}) (g : Aut F')
    (X : TrivialMonodromy F N) (x : F'.obj X.obj) :
    (trivialMonodromyRestrictionAt F N F' g).asIso.hom.app X x =
      g.asIso.hom.app X.obj x := rfl

/-- Change the restricted fibre using the restriction of the given natural
isomorphism, with its original components. -/
def trivialMonodromyFiberEquiv {F' F'' : C ⥤ FintypeCat.{w}} (t : F' ≅ F'') :
    Aut (trivialMonodromyInclusion F N ⋙ F') ≃ₜ*
      Aut (trivialMonodromyInclusion F N ⋙ F'') :=
  continuousConjAut (Functor.isoWhiskerLeft (trivialMonodromyInclusion F N) t)

/-- Fibre change commutes with restriction of the original automorphism group. -/
theorem trivialMonodromyFiberEquiv_restriction
    {F' F'' : C ⥤ FintypeCat.{w}} (t : F' ≅ F'') (g : Aut F') :
    trivialMonodromyFiberEquiv F N t (trivialMonodromyRestrictionAt F N F' g) =
      trivialMonodromyRestrictionAt F N F'' (continuousConjAut t g) := by
  apply Aut.ext
  apply Iso.ext
  ext X x
  rfl

/-- Triviality after restriction is invariant under the actual fibre comparison. -/
theorem trivialMonodromyRestrictionAt_conj_eq_one_iff
    {F' F'' : C ⥤ FintypeCat.{w}} (t : F' ≅ F'') (g : Aut F') :
    trivialMonodromyRestrictionAt F N F'' (continuousConjAut t g) = 1 ↔
      trivialMonodromyRestrictionAt F N F' g = 1 := by
  rw [← trivialMonodromyFiberEquiv_restriction F N t g]
  constructor
  · intro h
    apply (trivialMonodromyFiberEquiv F N t).injective
    exact h.trans (map_one (trivialMonodromyFiberEquiv F N t)).symm
  · intro h
    rw [h, map_one]

variable [GaloisCategory C]

/-- All original fibre functors restrict to isomorphic fibre functors on the
same full subcategory; the comparison comes from an actual original natural iso. -/
theorem nonempty_trivialMonodromyFiberIso
    (F' F'' : C ⥤ FintypeCat.{w}) [FiberFunctor F'] [FiberFunctor F''] :
    Nonempty (trivialMonodromyInclusion F N ⋙ F' ≅
      trivialMonodromyInclusion F N ⋙ F'') := by
  obtain ⟨t⟩ := nonempty_iso_of_exact F' F''
  exact ⟨Functor.isoWhiskerLeft (trivialMonodromyInclusion F N) t⟩

variable [FiberFunctor F]

/-- The original automorphism group surjects onto the restricted one at every
fibre functor, because the retained category is full. -/
theorem trivialMonodromyRestrictionAt_surjective
    (F' : C ⥤ FintypeCat.{w}) [FiberFunctor F'] :
    Function.Surjective (trivialMonodromyRestrictionAt F N F') := by
  have hff : Nonempty (trivialMonodromyInclusion F N).FullyFaithful :=
    ⟨(trivialMonodromy F N).fullyFaithfulι⟩
  exact ((autHomOfCompIso_surjective_tfae (trivialMonodromyInclusion F N ⋙ F') F'
    (trivialMonodromyInclusion F N) (Iso.refl _)).out 2 1).mp hff

end CategoryTheory.PreGaloisCategory
