/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Morphisms between given connected-component decompositions

For an arbitrary given finite coproduct, a morphism from a connected object
factors through one of its specified summands. The factor is constructed using
the actual pullback of that summand and the nonempty fiber of the source.
Applying this construction to every source summand gives the index map and
component morphisms for two given coproduct decompositions.

This supplies clause (8) of Stacks Project, Lemma 58.3.7 (tag `0BN0`).
The target summands need not themselves be connected. The source coproduct
can have any index type, provided its displayed colimit is supplied.

The proof reuses Mathlib's fiber pullback equivalence, connectedness criterion,
and concrete colimit representatives. It does not choose replacement
connected-component decompositions.
-/

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]

/-- A map from a connected object factors through one summand of any given finite coproduct. -/
theorem exists_factor_through_given_coproduct_injection
    {κ : Type w} [Finite κ] (Y : κ → C) {B X : C}
    (j : (k : κ) → Y k ⟶ B) (hY : IsColimit (Cofan.mk B j))
    [IsConnected X] (f : X ⟶ B) :
    ∃ (k : κ) (g : X ⟶ Y k), g ≫ j k = f := by
  let F : C ⥤ FintypeCat.{v} := CategoryTheory.GaloisCategory.getFiberFunctor C
  have : FiberFunctor F :=
    inferInstanceAs (FiberFunctor (CategoryTheory.GaloisCategory.getFiberFunctor C))
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
  let c : Cocone (Discrete.functor Y ⋙ F) := F.mapCocone (Cofan.mk B j)
  have hc : IsColimit c := isColimitOfPreserves F hY
  obtain ⟨⟨k⟩, y, hy⟩ := Concrete.isColimit_exists_rep _ hc (F.map f x)
  have hy' : F.map (j k) y = F.map f x := hy
  have : Mono (j k) := MonoCoprod.mono_inj _ (Cofan.mk B j) hY k
  let t : F.obj (pullback f (j k)) :=
    (fiberPullbackEquiv F f (j k)).symm ⟨(x, y), hy'.symm⟩
  have : IsIso (pullback.fst f (j k)) :=
    IsConnected.noTrivialComponent (pullback f (j k)) (pullback.fst f (j k))
      (not_initial_of_inhabited F t)
  refine ⟨k, inv (pullback.fst f (j k)) ≫ pullback.snd f (j k), ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

/-- Every morphism between given coproduct decompositions is the coproduct of its
constructed component morphisms along a map between the given index types.
In particular this applies to arbitrary finite connected-component decompositions. -/
theorem exists_component_maps_of_given_coproduct_decompositions
    {ι : Type z} {κ : Type w} [Finite κ]
    (X : ι → C) (Y : κ → C) {A B : C}
    (iX : (i : ι) → X i ⟶ A) (hX : IsColimit (Cofan.mk A iX))
    (iY : (k : κ) → Y k ⟶ B) (hY : IsColimit (Cofan.mk B iY))
    [∀ i : ι, IsConnected (X i)] (f : A ⟶ B) :
    ∃ (α : ι → κ) (g : (i : ι) → X i ⟶ Y (α i)),
      f = Cofan.IsColimit.desc hX (fun i => g i ≫ iY (α i)) := by
  choose α g hg using fun i : ι =>
    exists_factor_through_given_coproduct_injection Y iY hY (iX i ≫ f)
  refine ⟨α, g, ?_⟩
  apply Cofan.IsColimit.hom_ext hX
  intro i
  exact (hg i).symm.trans
    (Cofan.IsColimit.fac hX (fun k => g k ≫ iY (α k)) i).symm

end CategoryTheory.PreGaloisCategory
