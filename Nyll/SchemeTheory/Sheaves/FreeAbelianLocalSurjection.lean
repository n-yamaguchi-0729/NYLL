/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Algebra.Category.Grp.Adjunctions

/-!
# Free abelian sheaves of local surjections

A local surjection of presheaves induces an epimorphism after taking
free abelian groups and sheafifying. The proof uses separatedness and
the two defining adjunctions.
-/

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A local surjection can be cancelled when mapping into a sheaf. -/
theorem Presheaf.hom_ext_of_locallySurjective
    {P Q : Cᵒᵖ ⥤ Type w} (ρ : P ⟶ Q) [Presheaf.IsLocallySurjective J ρ]
    (F : Sheaf J (Type w)) (a b : Q ⟶ F.obj) (h : ρ ≫ a = ρ ≫ b) : a = b := by
  ext X x
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 F.property).isSeparated _
    (Presheaf.imageSieve_mem J ρ x)).ext
  rintro Y f ⟨s : P.obj (op Y), hs : ρ.app _ s = Q.map f.op x⟩
  dsimp
  have ha := ConcreteCategory.congr_hom (a.naturality f.op) x
  have hb := ConcreteCategory.congr_hom (b.naturality f.op) x
  dsimp at ha hb
  rw [← ha, ← hb, ← hs]
  exact ConcreteCategory.congr_hom (congr_app h (op Y)) s

/-- The free abelian sheaf functor sends local surjections to epimorphisms. -/
theorem epi_sheafify_free_of_locallySurjective
    [HasSheafify J AddCommGrpCat.{w}]
    {P Q : Cᵒᵖ ⥤ Type w} (ρ : P ⟶ Q) [Presheaf.IsLocallySurjective J ρ] :
    Epi ((presheafToSheaf J AddCommGrpCat.{w}).map
      (Functor.whiskerRight ρ AddCommGrpCat.free)) where
  left_cancellation {F} a b h := by
    let e₁ := (sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv
      (Q ⋙ AddCommGrpCat.free) F
    let e₂ := (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv Q F.obj
    apply e₁.injective
    apply e₂.injective
    apply Presheaf.hom_ext_of_locallySurjective J ρ
      ((sheafCompose J (forget AddCommGrpCat.{w})).obj F)
    have hh := congrArg
      ((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv
        (P ⋙ AddCommGrpCat.free) F) h
    rw [Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_left] at hh
    have hh' := congrArg
      ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv P F.obj) hh
    exact ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left
      ρ (e₁ a)).symm.trans (hh'.trans
        ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left ρ (e₁ b)))

end CategoryTheory
