/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.FinitePushforwardStalks
import Nyll.EtaleCohomology.Sites.GeometricStalkSectionDescent
import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.FieldTheory.SeparableClosure

/-!
# Equality of étale sheaf sections descends from the geometric stalk

Equality after actual inverse image forces the source into the open locus
where the original sections agree. For the strict-local base change of a
qcqs scheme, the map to this open spreads to a pointed affine étale stage.
Thus equal strict-local restrictions of original sections are already equal
at a finite stage. The coefficient sheaf is arbitrary, with no torsion or
constructibility hypothesis. This supplies the equality part of the degree
zero continuity argument in Stacks Project, Theorem 59.53.1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

universe u

/-- Equality after pulling through a local factor forces its whole image
into any open containing the étale equality locus of the original sections.
The source is an arbitrary object of the inverse-image small étale site. -/
theorem range_subset_sectionEquality_open_of_local_pullback_eq
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (V : Y.Etale) (U : X.Etale) (l : V.left ⟶ U.left)
    (hl : l ≫ U.hom = V.hom ≫ q)
    (a b : F.obj.obj (op U))
    (W : U.left.Opens)
    (hW : ∀ (T : X.Etale) (g : T ⟶ U),
      F.obj.map g.op a = F.obj.map g.op b → Set.range g.left ⊆ (W : Set U.left))
    (hab : etalePullbackSectionMap q Λ F (U := V) l hl a =
      etalePullbackSectionMap q Λ F (U := V) l hl b) :
    Set.range l ⊆ (W : Set U.left) := by
  rintro _ ⟨y, rfl⟩
  let Ω := SeparableClosure (V.left.residueField y)
  let s : Spec (CommRingCat.of Ω) ⟶ V.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (V.left.residueField y) Ω)) ≫
      V.left.fromSpecResidueField y
  let ξ : Spec (CommRingCat.of Ω) := default
  have hs : s ξ = y := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply y _
  let vhom : V.left ⟶ Y := V.hom
  let t : Spec (CommRingCat.of Ω) ⟶ Y := s ≫ vhom
  let Ψ := Scheme.pointSmallEtale t
  let Φ := Scheme.pointSmallEtale (t ≫ q)
  let u : Φ.fiber.obj U := by
    change Over.mk (t ≫ q) ⟶ Over.mk U.hom
    exact Over.homMk (s ≫ l) ((Category.assoc s l U.hom).trans
      ((congrArg (fun z : V.left ⟶ X => s ≫ z) hl).trans
        (Category.assoc s vhom q).symm))
  let yPoint : Ψ.fiber.obj V := by
    change Over.mk t ⟶ Over.mk V.hom
    exact Over.homMk s rfl
  let G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePullback q Λ).obj F
  let k : (Φ.sheafFiber (A := ModuleCat.{u} Λ)).obj F ⟶ Ψ.sheafFiber.obj G :=
    Φ.sheafFiber.map ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q (t ≫ q) ⟨t, rfl⟩ G
  have : IsIso k := etalePullbackUnit_stalkComponent_isIso q t Λ F
  have hmap : etalePullbackSectionMap q Λ F (U := V) l hl ≫
      Ψ.toPresheafFiber V yPoint G.obj = Φ.toPresheafFiber U u F.obj ≫ k :=
    etalePullbackSectionMap_toPresheafFiber q t Λ F (U := V) (V := U) l hl yPoint
  have hgerm : Φ.toPresheafFiber U u F.obj a = Φ.toPresheafFiber U u F.obj b := by
    apply (ModuleCat.mono_iff_injective k).mp inferInstance
    exact (ConcreteCategory.congr_hom hmap a).symm.trans
      ((congrArg (Ψ.toPresheafFiber V yPoint G.obj) hab).trans
        (ConcreteCategory.congr_hom hmap b))
  obtain ⟨T, g, v, hv, heq⟩ := (Φ.toPresheafFiber_eq_iff' U u a b).mp hgerm
  have hvl : v.left ≫ g.left = s ≫ l :=
    congrArg (fun z : Over.mk (t ≫ q) ⟶ Over.mk U.hom => z.left) hv
  have hvy : g.left (v.left ξ) = l y :=
    (Scheme.Hom.comp_apply v.left g.left ξ).symm.trans
      ((congrArg (fun z : Spec (CommRingCat.of Ω) ⟶ U.left => z ξ) hvl).trans
        ((Scheme.Hom.comp_apply s l ξ).trans (congrArg l hs)))
  exact hvy ▸ hW T g heq ⟨v.left ξ, rfl⟩

/-- Equal actual inverse images force the image into any open containing
every étale restriction on which the original sections agree. In particular,
this applies to the concrete maximal open supplied by `exists_sectionEquality_open`. -/
theorem range_subset_sectionEquality_open_of_pullback_eq
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : X.Etale) (l : Y ⟶ U.left) (hl : l ≫ U.hom = (𝟙 Y) ≫ q)
    (a b : F.obj.obj (op U))
    (W : U.left.Opens)
    (hW : ∀ (V : X.Etale) (g : V ⟶ U),
      F.obj.map g.op a = F.obj.map g.op b → Set.range g.left ⊆ (W : Set U.left))
    (hab : etalePullbackSectionMap q Λ F (U := Scheme.Etale.mk (𝟙 Y)) l hl a =
      etalePullbackSectionMap q Λ F (U := Scheme.Etale.mk (𝟙 Y)) l hl b) :
    Set.range l ⊆ (W : Set U.left) := by
  exact range_subset_sectionEquality_open_of_local_pullback_eq q Λ F
    (Scheme.Etale.mk (𝟙 Y)) U l hl a b W hW hab

/-- If two sections have equal actual inverse images, the map through their
étale object lands in an open on which the original sections agree. -/
theorem exists_sectionEquality_open_of_pullback_eq
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : X.Etale) (l : Y ⟶ U.left) (hl : l ≫ U.hom = (𝟙 Y) ≫ q)
    (a b : F.obj.obj (op U))
    (hab : etalePullbackSectionMap q Λ F (U := Scheme.Etale.mk (𝟙 Y)) l hl a =
      etalePullbackSectionMap q Λ F (U := Scheme.Etale.mk (𝟙 Y)) l hl b) :
    ∃ W : U.left.Opens, Set.range l ⊆ (W : Set U.left) ∧
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl :
        (Scheme.Etale.mk (W.ι ≫ U.hom) : X.Etale) ⟶ U).op a =
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl :
        (Scheme.Etale.mk (W.ι ≫ U.hom) : X.Etale) ⟶ U).op b := by
  have : X.smallEtaleTopology.HasSheafCompose (forget (ModuleCat.{u} Λ)) := by
    let : PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ)) :=
      (ModuleCat.adj Λ).rightAdjoint_preservesLimits
    exact hasSheafCompose_of_preservesLimitsOfSize
      (F := forget (ModuleCat.{u} Λ)) X.smallEtaleTopology
  obtain ⟨W, hW, habW⟩ := exists_sectionEquality_open F U a b
  exact ⟨W, range_subset_sectionEquality_open_of_pullback_eq q Λ F U l hl a b W hW hab,
    habW⟩

/-- Equality of actual strict-local pullbacks of two sections of an arbitrary
étale module sheaf holds after a pointed affine étale base change. The source
scheme is only qcqs over the affine base. -/
theorem geometricStalk_exists_affine_sectionEquality_stage
    {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (a b : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (hab :
      etalePullbackGlobalSectionsMap
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) Λ F a =
      etalePullbackGlobalSectionsMap
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) Λ F b) :
    ∃ (V : (Spec (.of R)).Etale)
      (_ : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V)
      (_ : IsAffine V.left),
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
        (pullback.snd V.hom f) (Category.comp_id _) :
        (Scheme.Etale.mk (pullback.snd V.hom f) : X.Etale) ⟶
          Scheme.Etale.mk (𝟙 X)).op a =
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
        (pullback.snd V.hom f) (Category.comp_id _) :
        (Scheme.Etale.mk (pullback.snd V.hom f) : X.Etale) ⟶
          Scheme.Etale.mk (𝟙 X)).op b := by
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let q : pullback h f ⟶ X := pullback.snd h f
  let U : X.Etale := Scheme.Etale.mk (𝟙 X)
  obtain ⟨W, hW, habW⟩ := exists_sectionEquality_open_of_pullback_eq q Λ F U q
    ((Category.comp_id q).trans (Category.id_comp q).symm) a b hab
  change X.Opens at W
  change Set.range q ⊆ (W : Set X) at hW
  have hRange : Set.range q ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact hW
  let s : pullback h f ⟶ W.toScheme := IsOpenImmersion.lift W.ι q hRange
  have hs : s ≫ W.ι = pullback.snd h f := IsOpenImmersion.lift_fac W.ι q hRange
  obtain ⟨V, v, hV, t, _, ht, _⟩ :=
    geometricStalk_exists_affine_section_stage φ f W.ι s hs
  let B : X.Etale := Scheme.Etale.mk (pullback.snd V.hom f)
  let O : X.Etale := Scheme.Etale.mk (W.ι ≫ 𝟙 X)
  let j : O ⟶ U := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
  let k : B ⟶ O := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) t (by
      change t ≫ (W.ι ≫ 𝟙 X) = pullback.snd V.hom f
      exact (congrArg (fun z => t ≫ z) (Category.comp_id W.ι)).trans ht)
  let r : B ⟶ U := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (pullback.snd V.hom f) (Category.comp_id _)
  have hkj : k ≫ j = r := MorphismProperty.Over.Hom.ext ht
  refine ⟨V, v, hV, ?_⟩
  change F.obj.map r.op a = F.obj.map r.op b
  have hr (x : F.obj.obj (op U)) :
      F.obj.map r.op x = F.obj.map k.op (F.obj.map j.op x) :=
    (congrArg (fun z : B ⟶ U => F.obj.map z.op x) hkj).symm.trans
      (F.obj.map_comp_apply j.op k.op x)
  exact (hr a).trans ((congrArg (F.obj.map k.op) habW).trans (hr b).symm)

end EtaleCohomology
