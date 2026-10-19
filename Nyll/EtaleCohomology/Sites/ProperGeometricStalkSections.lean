/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricStalkSectionComparison
import Nyll.EtaleCohomology.Sites.GeometricStalkSectionEquality
import Nyll.SchemeTheory.Etale.FiniteNeighborhoodSection
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Injectivity of the proper strict-local section comparison

For a universally closed morphism, the actual direct-image stalk embeds
in sections after actual base change to the constructed strict-local ring.
Equality after inverse image places the image of this base change in the
maximal equality-open. Its native Cartesian square shows that this image
contains the whole pointed fiber; universal closedness then shrinks the
original neighborhood and makes the represented germs equal.

No rational-point description of the fiber is used. The coefficient sheaf
is arbitrary, and universal closedness suffices for this injective half of
the proper degree-zero comparison in Stacks Project, Lemma 59.91.4.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual map to a neighborhood's source base change is Cartesian
over its canonical strictly local neighborhood map. -/
theorem geometricStalkNeighborhoodBaseChangeMap_isPullback
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    IsPullback (geometricStalkNeighborhoodBaseChangeMap φ f U v)
      (pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)
      (pullback.fst U.hom f) (geometricStalkNeighborhoodMap φ U v) := by
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let ρ := geometricStalkNeighborhoodMap φ U v
  let m := geometricStalkNeighborhoodBaseChangeMap φ f U v
  have hm : m ≫ pullback.snd U.hom f = pullback.snd h f :=
    geometricStalkNeighborhoodBaseChangeMap_snd φ f U v
  have hρ : ρ ≫ U.hom = h := geometricStalkNeighborhoodMap_comp φ U v
  have ho : IsPullback (m ≫ pullback.snd U.hom f) (pullback.fst h f) f (ρ ≫ U.hom) := by
    rw [hm, hρ]
    exact (IsPullback.of_hasPullback h f).flip
  exact ho.of_right (geometricStalkNeighborhoodBaseChangeMap_fst φ f U v)
    (IsPullback.of_hasPullback U.hom f).flip

/-- The range of the strictly local source base change contains every
point of the fiber over the specified geometric point of a neighborhood. -/
theorem geometricStalkNeighborhoodBaseChangeMap_pointFiber_subset_range
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U)
    (x : ((etaleBaseChange f).obj U).left)
    (hx : pullback.fst U.hom f x = v.left (default : Spec (CommRingCat.of Ω))) :
    x ∈ Set.range (geometricStalkNeighborhoodBaseChangeMap φ f U v) := by
  let j := Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)))
  let ρ := geometricStalkNeighborhoodMap φ U v
  have hj : ρ (j default) = v.left (default : Spec (CommRingCat.of Ω)) :=
    (Scheme.Hom.comp_apply j ρ default).symm.trans
      (congrArg (fun a : Spec (CommRingCat.of Ω) ⟶ U.left => a default)
        (geometricStalkNeighborhoodMap_evaluation φ U v))
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
    (geometricStalkNeighborhoodBaseChangeMap_isPullback φ f U v)
    x (j default) (hx.trans hj.symm)
  exact ⟨z, hz⟩

/-- The actual strict-local comparison for direct image is injective for
every universally closed morphism, in particular every proper morphism. -/
theorem etalePushforwardGeometricStalkSections_injective
    [UniversallyClosed f] (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Injective (etalePushforwardGeometricStalkSections φ f Λ F) := by
  intro a b hab
  obtain ⟨U, u, a, b, rfl, rfl⟩ :=
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_jointly_surjective₂
      a b
  let B : X.Etale := (etaleBaseChange f).obj U
  change F.obj.obj (op B) at a b
  change Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk U.hom at u
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let Y := pullback h f
  let q : Y ⟶ X := pullback.snd h f
  let m : Y ⟶ B.left := geometricStalkNeighborhoodBaseChangeMap φ f U u
  have hm : m ≫ B.hom = (𝟙 Y) ≫ q :=
    (geometricStalkNeighborhoodBaseChangeMap_snd φ f U u).trans (Category.id_comp q).symm
  have heq : geometricStalkNeighborhoodSectionMap φ f Λ F U u a =
      geometricStalkNeighborhoodSectionMap φ f Λ F U u b :=
    (ConcreteCategory.congr_hom
      (toPresheafFiber_etalePushforwardGeometricStalkSections φ f Λ F U u) a).symm.trans
      (hab.trans (ConcreteCategory.congr_hom
        (toPresheafFiber_etalePushforwardGeometricStalkSections φ f Λ F U u) b))
  obtain ⟨W, hW, habW⟩ := exists_sectionEquality_open_of_pullback_eq
    q Λ F B m hm a b heq
  let p : B.left ⟶ U.left := pullback.fst U.hom f
  have : UniversallyClosed p :=
    inferInstanceAs (UniversallyClosed (pullback.fst U.hom f))
  have hfiber : ∀ x : B.left, p x = u.left (default : Spec (CommRingCat.of Ω)) → x ∈ W := by
    intro x hx
    exact hW (geometricStalkNeighborhoodBaseChangeMap_pointFiber_subset_range φ f U u x hx)
  obtain ⟨V, hV, hVW⟩ := p.exists_preimage_le_of_fiber_subset
    (u.left (default : Spec (CommRingCat.of Ω))) W hfiber
  have huRange : Set.range u.left ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨z, rfl⟩
    have hz : z = (default : Spec (CommRingCat.of Ω)) :=
      Subsingleton.elim (show Spec (CommRingCat.of Ω) from z) _
    rw [hz]
    exact hV
  let v : Spec (CommRingCat.of Ω) ⟶ V.toScheme := IsOpenImmersion.lift V.ι u.left huRange
  have hv : v ≫ V.ι = u.left := IsOpenImmersion.lift_fac V.ι u.left huRange
  let T : (Spec (CommRingCat.of R)).Etale := Scheme.Etale.mk (V.ι ≫ U.hom)
  let g : T ⟶ U := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) V.ι rfl
  let w : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj T :=
    Over.homMk v (by
      change v ≫ (V.ι ≫ U.hom) = Spec.map (CommRingCat.ofHom φ)
      rw [← Category.assoc, hv]
      exact u.w)
  have hw : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map g w = u := by
    apply Over.OverMorphism.ext
    exact hv
  let n : ((etaleBaseChange f).obj T).left ⟶ B.left := ((etaleBaseChange f).map g).left
  let pT : ((etaleBaseChange f).obj T).left ⟶ V.toScheme := pullback.fst T.hom f
  have hnp : n ≫ p = pT ≫ V.ι := pullback.lift_fst _ _ _
  have hnRange : Set.range n ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨z, rfl⟩
    apply hVW
    change p (n z) ∈ V
    rw [← Scheme.Hom.comp_apply, hnp, Scheme.Hom.comp_apply]
    exact (pT z).property
  let l : ((etaleBaseChange f).obj T).left ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι n hnRange
  have hl : l ≫ W.ι = n := IsOpenImmersion.lift_fac W.ι n hnRange
  let O : X.Etale := Scheme.Etale.mk (W.ι ≫ B.hom)
  let j : O ⟶ B := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
  let k : (etaleBaseChange f).obj T ⟶ O := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) l (by
      change l ≫ (W.ι ≫ B.hom) = ((etaleBaseChange f).obj T).hom
      rw [← Category.assoc, hl]
      exact ((etaleBaseChange f).map g).w)
  have hkj : k ≫ j = (etaleBaseChange f).map g := MorphismProperty.Over.Hom.ext hl
  apply ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_eq_iff'
    (P := ((etalePushforward f Λ).obj F).obj) U u a b).mpr
  refine ⟨T, g, w, hw, ?_⟩
  change F.obj.map ((etaleBaseChange f).map g).op a = F.obj.map ((etaleBaseChange f).map g).op b
  rw [← hkj, op_comp, F.obj.map_comp_apply, F.obj.map_comp_apply]
  exact congrArg (F.obj.map k.op) habW

end EtaleCohomology
