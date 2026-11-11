/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCategories.PointedOver
public import Mathlib.CategoryTheory.Galois.GaloisObjects

/-!
# Relative deck transitivity

A Galois object remains Galois over an intermediate object. Here the
essential transitivity assertion is proved directly on the actual
fiber-over-a-point functor, constructing each relative deck automorphism.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

/-- Original deck transitivity restricts to every fiber of an intermediate
morphism. The relative deck transformations are actual over-category isomorphisms. -/
theorem relativeDeck_isPretransitive
    {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    {A B : C} [IsGalois A] (f : A ⟶ B) (y : F.obj B) :
    MulAction.IsPretransitive (Aut (Over.mk f))
      ((fiberOver F y).obj (Over.mk f)) := by
  constructor
  intro a b
  change { z : F.obj A // F.map f z = y } at a b
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut A) a.1 b.1
  change F.map σ.asIso.hom a.1 = b.1 at hσ
  have hf : σ.asIso.hom ≫ f = f := by
    apply evaluation_injective_of_isConnected F A B a.1
    change F.map (σ.asIso.hom ≫ f) a.1 = F.map f a.1
    rw [F.map_comp, FintypeCat.comp_apply, hσ]
    exact b.2.trans a.2.symm
  let τ : Aut (Over.mk f) := Aut.of (Over.isoMk σ.asIso hf)
  refine ⟨τ, ?_⟩
  apply Subtype.ext
  exact hσ

end CategoryTheory.PreGaloisCategory
