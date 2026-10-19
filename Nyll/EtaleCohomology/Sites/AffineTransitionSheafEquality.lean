/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricStalkSectionEquality
import Nyll.EtaleCohomology.Sites.PullbackSections
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Equality of sheaf sections at an affine-transition limit

Two sections on a stage whose actual inverse images agree on the limit
already agree after inverse image to a later stage. The equality locus is
an actual open subset of the original stage. Quasi-compactness and affine
transition maps spread the inclusion of the limit's image in this open.

The coefficient sheaf is arbitrary, and the stage maps need not be étale.
This is the equality step needed when gluing finite local representatives
in degree-zero continuity for étale sheaves (Stacks Project, Theorem 59.53.1).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

universe u

private theorem pullbackGlobalSections_eq_of_localFactor
    {X Y : Scheme.{u}} (q : Y ⟶ X) (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (V : X.Etale) (g : V ⟶ Scheme.Etale.mk (𝟙 X))
    (l : Y ⟶ V.left) (hl : l ≫ V.hom = (𝟙 Y) ≫ q)
    (a b : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (hab : F.obj.map g.op a = F.obj.map g.op b) :
    etalePullbackGlobalSectionsMap q Λ F a = etalePullbackGlobalSectionsMap q Λ F b := by
  let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePullback q Λ).obj F
  let r : T ⟶ T := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (𝟙 Y) (Category.comp_id _)
  have hr : r = 𝟙 T := MorphismProperty.Over.Hom.ext rfl
  have hn : F.obj.map g.op ≫ etalePullbackSectionMap q Λ F (U := T) l hl =
      etalePullbackGlobalSectionsMap q Λ F ≫ G.obj.map r.op :=
    etalePullbackSectionMap_global_restriction q Λ F (U := T) (V := V) g l hl
  rw [hr, op_id, G.obj.map_id, Category.comp_id] at hn
  have he (x : F.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
      etalePullbackGlobalSectionsMap q Λ F x =
        etalePullbackSectionMap q Λ F (U := T) l hl (F.obj.map g.op x) :=
    (ConcreteCategory.congr_hom hn x).symm
  exact (he a).trans
    ((congrArg (etalePullbackSectionMap q Λ F (U := T) l hl) hab).trans (he b).symm)

/-- Equality after actual inverse image to a cofiltered limit of
quasi-compact schemes with affine transitions is witnessed at a stage.
No quasi-separatedness or finite-presentation hypothesis is required. -/
theorem exists_pullback_globalSections_eq_of_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    (i : I) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (D.obj i).smallEtaleTopology (ModuleCat.{u} Λ))
    (a b : F.obj.obj (op (Scheme.Etale.mk (𝟙 (D.obj i)))))
    (hab : etalePullbackGlobalSectionsMap (c.π.app i) Λ F a =
      etalePullbackGlobalSectionsMap (c.π.app i) Λ F b) :
    ∃ (j : I) (f : j ⟶ i),
      etalePullbackGlobalSectionsMap (D.map f) Λ F a =
        etalePullbackGlobalSectionsMap (D.map f) Λ F b := by
  let X := D.obj i
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  obtain ⟨W, hW, habW⟩ := exists_sectionEquality_open_of_pullback_eq
    (c.π.app i) Λ F T (c.π.app i)
      ((Category.comp_id _).trans (Category.id_comp _).symm) a b hab
  change X.Opens at W
  change Set.range (c.π.app i) ⊆ (W : Set X) at hW
  have htop : c.π.app i ⁻¹ᵁ W = ⊤ := by
    apply top_unique
    intro x _
    exact hW ⟨x, rfl⟩
  obtain ⟨j, f, hf⟩ := exists_map_eq_top D c hc W htop
  let p : D.obj j ⟶ X := D.map f
  have hRange : Set.range p ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hf.ge (Set.mem_univ x)
  let l : D.obj j ⟶ W.toScheme := IsOpenImmersion.lift W.ι p hRange
  have hl : l ≫ W.ι = p := IsOpenImmersion.lift_fac W.ι p hRange
  let O : X.Etale := Scheme.Etale.mk (W.ι ≫ 𝟙 X)
  let e : O ⟶ T := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
  let Tj : (D.obj j).Etale := Scheme.Etale.mk (𝟙 (D.obj j))
  have hl' : l ≫ O.hom = Tj.hom ≫ p := by
    change l ≫ (W.ι ≫ 𝟙 X) = (𝟙 (D.obj j)) ≫ p
    rw [Category.comp_id, Category.id_comp]
    exact hl
  refine ⟨j, f, ?_⟩
  exact pullbackGlobalSections_eq_of_localFactor p Λ F O e l hl' a b habW

end EtaleCohomology
