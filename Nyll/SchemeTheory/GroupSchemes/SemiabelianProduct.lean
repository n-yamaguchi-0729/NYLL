/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Semiabelian
import Nyll.SchemeTheory.GroupSchemes.TorusProduct
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Products of actual semiabelian extensions -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupSchemes

variable {S : Scheme.{u}}

/-- The componentwise morphism between actual product group schemes. -/
def productMap {G G' H H' : CommGrp (Over S)} (f : G ⟶ G') (g : H ⟶ H') :
    product G H ⟶ product G' H' := by
  have : IsMonHom f.hom.hom.hom := f.hom.hom.isMonHom_hom
  have : IsMonHom g.hom.hom.hom := g.hom.hom.isMonHom_hom
  let m : G.X ⊗ H.X ⟶ G'.X ⊗ H'.X := f.hom.hom.hom ⊗ₘ g.hom.hom.hom
  have hm : IsMonHom m := by
    change IsMonHom (f.hom.hom.hom ⊗ₘ g.hom.hom.hom)
    infer_instance
  exact InducedCategory.homMk (Grp.homMk' { hom := m, isMonHom_hom := hm })

/-- A property stable under composition and base change holds for the componentwise product map. -/
theorem productMap_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {G G' H H' : CommGrp (Over S)} (f : G ⟶ G') (g : H ⟶ H')
    (hf : P f.hom.hom.hom.left) (hg : P g.hom.hom.hom.left) :
    P (productMap f g).hom.hom.hom.left := by
  change P (f.hom.hom.hom ⊗ₘ g.hom.hom.hom).left
  rw [Over.tensorHom_left]
  exact P.pullbackMap hf hg (Over.w f.hom.hom.hom).symm (Over.w g.hom.hom.hom).symm

end AlgebraicGeometry.GroupSchemes

namespace AlgebraicGeometry.SemiabelianExtension

variable {K : Type u} [Field K] {G H : CommGrp (Over (Spec (CommRingCat.of K)))}

private theorem comp_tensorHom_fst
    {X Y X' Y' T : Over (Spec (CommRingCat.of K))}
    (m : T ⟶ X ⊗ Y) (f : X ⟶ X') (g : Y ⟶ Y') :
    (m ≫ fst X Y) ≫ f = (m ≫ (f ⊗ₘ g)) ≫ fst X' Y' := by
  simp only [Category.assoc, tensorHom_fst]

private theorem comp_tensorHom_snd
    {X Y X' Y' T : Over (Spec (CommRingCat.of K))}
    (m : T ⟶ X ⊗ Y) (f : X ⟶ X') (g : Y ⟶ Y') :
    (m ≫ snd X Y) ≫ g = (m ≫ (f ⊗ₘ g)) ≫ snd X' Y' := by
  simp only [Category.assoc, tensorHom_snd]

private theorem product_condition (E : SemiabelianExtension G) (F : SemiabelianExtension H) :
    (GroupSchemes.productMap E.inclusion F.inclusion).hom.hom.hom ≫
      (GroupSchemes.productMap E.projection F.projection).hom.hom.hom = 1 := by
  change (E.inclusion.hom.hom.hom ⊗ₘ F.inclusion.hom.hom.hom) ≫
    (E.projection.hom.hom.hom ⊗ₘ F.projection.hom.hom.hom) = 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, tensorHom_fst_assoc,
      E.condition, MonObj.comp_one, MonObj.one_comp]
  · simp only [Category.assoc, tensorHom_snd, tensorHom_snd_assoc,
      F.condition, MonObj.comp_one, MonObj.one_comp]

private def product_kernel (E : SemiabelianExtension G) (F : SemiabelianExtension H) :
    IsLimit (Fork.ofι
      (GroupSchemes.productMap E.inclusion F.inclusion).hom.hom.hom
      ((product_condition E F).trans
        (MonObj.comp_one (GroupSchemes.productMap E.inclusion F.inclusion).hom.hom.hom).symm)) := by
  refine Fork.IsLimit.mk' _ fun s => ?_
  have h₁ : (s.ι ≫ fst G.X H.X) ≫ E.projection.hom.hom.hom = 1 := by
    have h := congrArg (fun z => z ≫ fst E.quotient.X F.quotient.X) s.condition
    change (s.ι ≫ (E.projection.hom.hom.hom ⊗ₘ F.projection.hom.hom.hom)) ≫
      fst E.quotient.X F.quotient.X = (s.ι ≫ 1) ≫ fst E.quotient.X F.quotient.X at h
    simp only [MonObj.one_comp, MonObj.comp_one] at h
    exact (comp_tensorHom_fst s.ι E.projection.hom.hom.hom F.projection.hom.hom.hom).trans h
  have h₂ : (s.ι ≫ snd G.X H.X) ≫ F.projection.hom.hom.hom = 1 := by
    have h := congrArg (fun z => z ≫ snd E.quotient.X F.quotient.X) s.condition
    change (s.ι ≫ (E.projection.hom.hom.hom ⊗ₘ F.projection.hom.hom.hom)) ≫
      snd E.quotient.X F.quotient.X = (s.ι ≫ 1) ≫ snd E.quotient.X F.quotient.X at h
    simp only [MonObj.one_comp, MonObj.comp_one] at h
    exact (comp_tensorHom_snd s.ι E.projection.hom.hom.hom F.projection.hom.hom.hom).trans h
  let u₁ := Fork.IsLimit.lift E.isKernel (s.ι ≫ fst G.X H.X)
    (h₁.trans (MonObj.comp_one (s.ι ≫ fst G.X H.X)).symm)
  let u₂ := Fork.IsLimit.lift F.isKernel (s.ι ≫ snd G.X H.X)
    (h₂.trans (MonObj.comp_one (s.ι ≫ snd G.X H.X)).symm)
  have hu₁ : u₁ ≫ E.inclusion.hom.hom.hom = s.ι ≫ fst G.X H.X :=
    Fork.IsLimit.lift_ι' E.isKernel _ _
  have hu₂ : u₂ ≫ F.inclusion.hom.hom.hom = s.ι ≫ snd G.X H.X :=
    Fork.IsLimit.lift_ι' F.isKernel _ _
  refine ⟨lift u₁ u₂, ?_, ?_⟩
  · change lift u₁ u₂ ≫ (E.inclusion.hom.hom.hom ⊗ₘ F.inclusion.hom.hom.hom) = s.ι
    rw [lift_map]
    exact CartesianMonoidalCategory.hom_ext _ _
      ((lift_fst _ _).trans hu₁) ((lift_snd _ _).trans hu₂)
  · intro m hm
    have hm₁ : m ≫ fst E.torus.X F.torus.X = u₁ := by
      apply Fork.IsLimit.hom_ext E.isKernel
      calc
        (m ≫ fst _ _) ≫ E.inclusion.hom.hom.hom =
            (m ≫ (GroupSchemes.productMap E.inclusion F.inclusion).hom.hom.hom) ≫ fst _ _ := by
          exact comp_tensorHom_fst m E.inclusion.hom.hom.hom F.inclusion.hom.hom.hom
        _ = s.ι ≫ fst _ _ := congrArg (fun z => z ≫ fst G.X H.X) hm
        _ = u₁ ≫ E.inclusion.hom.hom.hom := hu₁.symm
    have hm₂ : m ≫ snd E.torus.X F.torus.X = u₂ := by
      apply Fork.IsLimit.hom_ext F.isKernel
      calc
        (m ≫ snd _ _) ≫ F.inclusion.hom.hom.hom =
            (m ≫ (GroupSchemes.productMap E.inclusion F.inclusion).hom.hom.hom) ≫ snd _ _ := by
          exact comp_tensorHom_snd m E.inclusion.hom.hom.hom F.inclusion.hom.hom.hom
        _ = s.ι ≫ snd _ _ := congrArg (fun z => z ≫ snd G.X H.X) hm
        _ = u₂ ≫ F.inclusion.hom.hom.hom := hu₂.symm
    exact CartesianMonoidalCategory.hom_ext _ _
      (hm₁.trans (lift_fst _ _).symm) (hm₂.trans (lift_snd _ _).symm)

/-- Products of actual semiabelian extensions have the product torus kernel and abelian quotient. -/
def product (E : SemiabelianExtension G) (F : SemiabelianExtension H) :
    SemiabelianExtension (GroupSchemes.product G H) where
  torus := GroupSchemes.product E.torus F.torus
  quotient := GroupSchemes.product E.quotient F.quotient
  inclusion := GroupSchemes.productMap E.inclusion F.inclusion
  projection := GroupSchemes.productMap E.projection F.projection
  condition := product_condition E F
  isKernel := product_kernel E F
  projection_smooth := GroupSchemes.productMap_property (@Smooth) E.projection F.projection
    E.projection_smooth F.projection_smooth
  projection_surjective := by
    have : MorphismProperty.IsStableUnderComposition
        (@Surjective : MorphismProperty Scheme.{u}) :=
      { comp_mem := fun _ _ hf hg => ⟨hg.1.comp hf.1⟩ }
    exact GroupSchemes.productMap_property (@Surjective) E.projection F.projection
      E.projection_surjective F.projection_surjective

end AlgebraicGeometry.SemiabelianExtension

namespace AlgebraicGeometry.IsSemiabelian

variable {K : Type u} [Field K] {G H : CommGrp (Over (Spec (CommRingCat.of K)))}

/-- The actual componentwise product of semiabelian varieties is semiabelian. -/
instance product [IsSemiabelian G] [IsSemiabelian H] :
    IsSemiabelian (GroupSchemes.product G H) := by
  obtain ⟨E⟩ := exists_extension (G := G)
  obtain ⟨F⟩ := exists_extension (G := H)
  exact (E.product F).isSemiabelian

end AlgebraicGeometry.IsSemiabelian
