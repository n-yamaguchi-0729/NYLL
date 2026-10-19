/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionHom
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Descending an affine open étale covering from an inverse limit

An affine open in a base-changed étale model which covers the limiting
scheme descends to a covering affine open at a coefficient stage. Native
pullback squares retain the exact inverse-image open. The original source
is only quasi-compact; finite presentation of that source is not used.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineTransitionHom

variable {S T X U : Scheme.{u}}

/-- The actual map between native base changes induced by a map of models. -/
def modelMap (h : T ⟶ S) (f : X ⟶ S) (g : U ⟶ X) :
    pullback h (g ≫ f) ⟶ pullback h f :=
  pullback.lift (pullback.fst h (g ≫ f)) (pullback.snd h (g ≫ f) ≫ g)
    ((pullback.condition (f := h) (g := g ≫ f)).trans
      (Category.assoc (pullback.snd h (g ≫ f)) g f).symm)

theorem modelMap_fst (h : T ⟶ S) (f : X ⟶ S) (g : U ⟶ X) :
    modelMap h f g ≫ pullback.fst h f = pullback.fst h (g ≫ f) :=
  pullback.lift_fst _ _ _

theorem modelMap_snd (h : T ⟶ S) (f : X ⟶ S) (g : U ⟶ X) :
    modelMap h f g ≫ pullback.snd h f = pullback.snd h (g ≫ f) ≫ g :=
  pullback.lift_snd _ _ _

/-- Changing the model is the base change of its structure morphism. -/
theorem modelMap_isPullback (h : T ⟶ S) (f : X ⟶ S) (g : U ⟶ X) :
    IsPullback (modelMap h f g) (pullback.snd h (g ≫ f)) (pullback.snd h f) g := by
  have ho : IsPullback (modelMap h f g ≫ pullback.fst h f)
      (pullback.snd h (g ≫ f)) h (g ≫ f) := by
    rw [modelMap_fst]
    exact IsPullback.of_hasPullback h (g ≫ f)
  exact ho.of_right (modelMap_snd h f g) (IsPullback.of_hasPullback h f)

/-- Coefficient transition maps and model maps form the actual Cartesian square. -/
theorem modelMap_transition_isPullback {B C : Over S} (a : B ⟶ C)
    (f : X ⟶ S) (g : U ⟶ X) :
    IsPullback ((Over.pullback (g ≫ f)).map a).left (modelMap B.hom f g)
      (modelMap C.hom f g) ((Over.pullback f).map a).left := by
  let u : pullback B.hom (g ≫ f) ⟶ pullback C.hom (g ≫ f) :=
    ((Over.pullback (g ≫ f)).map a).left
  let x : pullback B.hom f ⟶ pullback C.hom f := ((Over.pullback f).map a).left
  have hu : u ≫ pullback.snd C.hom (g ≫ f) = pullback.snd B.hom (g ≫ f) :=
    Over.w ((Over.pullback (g ≫ f)).map a)
  have hx : x ≫ pullback.snd C.hom f = pullback.snd B.hom f :=
    Over.w ((Over.pullback f).map a)
  have huf : u ≫ pullback.fst C.hom (g ≫ f) =
      pullback.fst B.hom (g ≫ f) ≫ a.left := pullback.lift_fst _ _ _
  have hxf : x ≫ pullback.fst C.hom f = pullback.fst B.hom f ≫ a.left :=
    pullback.lift_fst _ _ _
  have hw : u ≫ modelMap C.hom f g = modelMap B.hom f g ≫ x := by
    apply pullback.hom_ext
    · rw [Category.assoc, modelMap_fst, huf, Category.assoc, hxf,
        ← Category.assoc, modelMap_fst]
    · rw [Category.assoc, modelMap_snd, ← Category.assoc, hu,
        Category.assoc, hx, modelMap_snd]
  have ho : IsPullback (u ≫ pullback.snd C.hom (g ≫ f))
      (modelMap B.hom f g) g (x ≫ pullback.snd C.hom f) := by
    rw [hu, hx]
    exact (modelMap_isPullback B.hom f g).flip
  exact ho.of_right hw (modelMap_isPullback C.hom f g).flip

private theorem range_open_comp {Y Z : Scheme.{u}} (V : Y.Opens) (p : Y ⟶ Z) :
    Set.range (V.ι ≫ p) = p '' (V : Set Y) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]

/-- Images of the descended opens commute with coefficient base change. -/
theorem modelMap_range_preimage {B C : Over S} (a : B ⟶ C)
    (f : X ⟶ S) (g : U ⟶ X) (V : (pullback C.hom (g ≫ f)).Opens) :
    Set.range ((((Over.pullback (g ≫ f)).map a).left ⁻¹ᵁ V).ι ≫ modelMap B.hom f g) =
      ((Over.pullback f).map a).left ⁻¹' Set.range (V.ι ≫ modelMap C.hom f g) := by
  rw [range_open_comp, range_open_comp]
  exact Scheme.image_preimage_eq_of_isPullback (modelMap_transition_isPullback a f g)
    V.carrier

/-- An affine open étale covering of a limiting model descends to an
affine open covering at a coefficient stage, with its actual inverse image. -/
theorem exists_affineOpen_cover_stage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    [∀ i : I, CompactSpace (D.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (D.obj i).left]
    (f : X ⟶ S) [QuasiCompact f] (g : U ⟶ X) [Etale g]
    [QuasiSeparated (g ≫ f)]
    (W : (pullback c.pt.hom (g ≫ f)).Opens) (hW : IsAffineOpen W)
    [hWsurj : Surjective (W.ι ≫ modelMap c.pt.hom f g)] :
    ∃ (i : I) (V : (pullback (D.obj i).hom (g ≫ f)).Opens),
      IsAffineOpen V ∧ (cone D c (g ≫ f)).π.app i ⁻¹ᵁ V = W ∧
      Surjective (V.ι ≫ modelMap (D.obj i).hom f g) := by
  have : ∀ {i j : I} (a : i ⟶ j), IsAffineHom ((diagram D (g ≫ f)).map a) :=
    fun a => diagram_map_isAffineHom D (g ≫ f) a
  have : ∀ i : I, QuasiSeparatedSpace ((diagram D (g ≫ f)).obj i) :=
    diagram_obj_quasiSeparatedSpace D (g ≫ f)
  have : ∀ {i j : I} (a : i ⟶ j), IsAffineHom ((diagram D f).map a) :=
    fun a => diagram_map_isAffineHom D f a
  have : ∀ i : I, CompactSpace ((diagram D f).obj i) := diagram_obj_compactSpace D f
  obtain ⟨i, V, hV, heq⟩ := exists_isAffineOpen_preimage_eq
    (diagram D (g ≫ f)) (cone D c (g ≫ f)) (coneIsLimit D c hc (g ≫ f)) W hW
  have : Etale (modelMap (D.obj i).hom f g) :=
    MorphismProperty.of_isPullback (P := show MorphismProperty Scheme.{u} from @Etale)
      (modelMap_isPullback (D.obj i).hom f g).flip inferInstance
  let O : ((diagram D f).obj i).Opens :=
    ⟨Set.range (V.ι ≫ modelMap (D.obj i).hom f g),
      (V.ι ≫ modelMap (D.obj i).hom f g).isOpenMap.isOpen_range⟩
  have htop : (cone D c f).π.app i ⁻¹ᵁ O = ⊤ := by
    apply SetLike.coe_injective
    change (cone D c f).π.app i ⁻¹' Set.range (V.ι ≫ modelMap (D.obj i).hom f g) = Set.univ
    have h := modelMap_range_preimage (c.π.app i) f g V
    change Set.range (((cone D c (g ≫ f)).π.app i ⁻¹ᵁ V).ι ≫ modelMap c.pt.hom f g) = _ at h
    rw [heq] at h
    exact h.symm.trans (Set.range_eq_univ.mpr (W.ι ≫ modelMap c.pt.hom f g).surjective)
  obtain ⟨j, a, ha⟩ := exists_map_eq_top (diagram D f) (cone D c f)
    (coneIsLimit D c hc f) O htop
  let Vj : ((diagram D (g ≫ f)).obj j).Opens := (diagram D (g ≫ f)).map a ⁻¹ᵁ V
  refine ⟨j, Vj, hV.preimage _, ?_, ?_⟩
  · change (cone D c (g ≫ f)).π.app j ⁻¹ᵁ
        ((diagram D (g ≫ f)).map a ⁻¹ᵁ V) = W
    rw [← Scheme.Hom.comp_preimage, (cone D c (g ≫ f)).w a, heq]
  · refine ⟨Set.range_eq_univ.mp ?_⟩
    change Set.range ((((Over.pullback (g ≫ f)).map (D.map a)).left ⁻¹ᵁ V).ι ≫
      modelMap (D.obj j).hom f g) = Set.univ
    rw [modelMap_range_preimage]
    exact congrArg (fun O : ((diagram D f).obj j).Opens =>
      (O : Set ((diagram D f).obj j))) ha

end AlgebraicGeometry.AffineTransitionHom
