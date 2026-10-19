/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.FiniteCoproductSections
import Nyll.EtaleCohomology.Classical.InjectiveCechSections
import Nyll.EtaleFundamentalGroups.GaloisCovers.TripleProduct
import Mathlib.Tactic.Abel
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.Grp.AB

/-!
# Actual Galois Cech cocycles

The deck-coordinate equivalence is additive. Triple deck graphs test the
actual geometric Cech identity, with the contravariant deck action.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace EtaleCohomology

/-- The actual deck-coordinate equivalence respects abelian coefficients. -/
def galoisSelfProductSectionsAddEquiv
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] :
    F.obj.obj (op ((finiteEtaleInclusion X).obj (Y ⨯ Y))) ≃+
      (Aut Y → F.obj.obj (op ((finiteEtaleInclusion X).obj Y))) where
  toEquiv := galoisSelfProductSectionsEquiv X
    ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F) Y
  map_add' s t := by
    funext σ
    let U := (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F
    have he (x : F.obj.obj (op ((finiteEtaleInclusion X).obj (Y ⨯ Y)))) :
        (galoisSelfProductSectionsEquiv X U Y x σ :
          F.obj.obj (op ((finiteEtaleInclusion X).obj Y))) =
        F.obj.map ((finiteEtaleInclusion X).map (prod.lift (𝟙 Y) σ.hom)).op x :=
      galoisSelfProductSectionsEquiv_apply X U Y x σ
    exact (he (s + t)).trans
      (((F.obj.map ((finiteEtaleInclusion X).map
        (prod.lift (𝟙 Y) σ.hom)).op).hom.map_add s t).trans
        (congrArg₂ (fun a b : F.obj.obj (op ((finiteEtaleInclusion X).obj Y)) => a + b)
          (he s).symm (he t).symm))

/-- Restriction to a graph gives the corresponding coordinate. -/
theorem galoisSelfProductSectionsAddEquiv_apply
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y]
    (s : F.obj.obj (op ((finiteEtaleInclusion X).obj (Y ⨯ Y)))) (σ : Aut Y) :
    galoisSelfProductSectionsAddEquiv X F Y s σ =
      F.obj.map ((finiteEtaleInclusion X).map (prod.lift (𝟙 Y) σ.hom)).op s :=
  galoisSelfProductSectionsEquiv_apply X
    ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F) Y s σ

/-- Actual triple deck graphs determine a section on the triple product. -/
theorem galoisTripleProduct_sections_ext
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology (Type u))
    (Y : FiniteEtale X) [IsGalois Y]
    (s t : F.obj.obj (op ((finiteEtaleInclusion X).obj (Y ⨯ (Y ⨯ Y)))))
    (h : ∀ σ τ : Aut Y,
      F.obj.map ((finiteEtaleInclusion X).map (galoisTripleGraph Y σ τ)).op s =
        F.obj.map ((finiteEtaleInclusion X).map (galoisTripleGraph Y σ τ)).op t) :
    s = t := by
  apply (F.obj.mapIso ((finiteEtaleInclusion X).mapIso
    (galoisTripleProductIso Y)).op).toEquiv.injective
  apply finiteEtale_sheaf_coproduct_sections_ext X F (fun _ : Aut Y × Aut Y => Y)
  intro p
  change F.obj.map ((finiteEtaleInclusion X).map
      (Sigma.ι (fun _ : Aut Y × Aut Y => Y) p)).op
    (F.obj.map ((finiteEtaleInclusion X).map (galoisTripleProductIso Y).hom).op s) =
    F.obj.map ((finiteEtaleInclusion X).map
      (Sigma.ι (fun _ : Aut Y × Aut Y => Y) p)).op
    (F.obj.map ((finiteEtaleInclusion X).map (galoisTripleProductIso Y).hom).op t)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    galoisTripleProductIso_ι]
  exact h p.1 p.2

/-- An actual contravariant deck cocycle gives an actual Cech cocycle
on the triple product, not merely a formal group-cohomology class. -/
theorem galoisCechSection_triangle
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y]
    (c : Aut Y → F.obj.obj (op ((finiteEtaleInclusion X).obj Y)))
    (hc : ∀ σ τ : Aut Y, c (τ * σ) =
      F.obj.map ((finiteEtaleInclusion X).map σ.hom).op (c τ) + c σ) :
    let z := (galoisSelfProductSectionsAddEquiv X F Y).symm c
    F.obj.map ((finiteEtaleInclusion X).map
        (prod.snd : Y ⨯ (Y ⨯ Y) ⟶ Y ⨯ Y)).op z -
      F.obj.map ((finiteEtaleInclusion X).map
        (prod.lift prod.fst (prod.snd ≫ prod.snd) : Y ⨯ (Y ⨯ Y) ⟶ Y ⨯ Y)).op z +
      F.obj.map ((finiteEtaleInclusion X).map
        (prod.lift prod.fst (prod.snd ≫ prod.fst) : Y ⨯ (Y ⨯ Y) ⟶ Y ⨯ Y)).op z = 0 := by
  let I := finiteEtaleInclusion X
  let z := (galoisSelfProductSectionsAddEquiv X F Y).symm c
  have hcoord (σ : Aut Y) :
      F.obj.map (I.map (prod.lift (𝟙 Y) σ.hom)).op z = c σ := by
    rw [← galoisSelfProductSectionsAddEquiv_apply]
    exact congrFun ((galoisSelfProductSectionsAddEquiv X F Y).apply_symm_apply c) σ
  apply galoisTripleProduct_sections_ext X
    ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F) Y
  intro σ τ
  have h₂₃ : galoisTripleGraph Y σ τ ≫ prod.snd =
      σ.hom ≫ prod.lift (𝟙 Y) τ.hom := by
    apply prod.hom_ext
    · simp only [galoisTripleGraph, prod.lift_snd, prod.lift_fst, Category.assoc,
        Category.comp_id]
    · simp only [galoisTripleGraph, prod.lift_snd, Category.assoc]
  have h₁₃ : galoisTripleGraph Y σ τ ≫
      prod.lift prod.fst (prod.snd ≫ prod.snd) = prod.lift (𝟙 Y) (τ * σ).hom := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, galoisTripleGraph]
    · simp only [Category.assoc, prod.lift_snd, galoisTripleGraph]
      rw [← Category.assoc, prod.lift_snd, prod.lift_snd]
      rfl
  have h₁₂ : galoisTripleGraph Y σ τ ≫
      prod.lift prod.fst (prod.snd ≫ prod.fst) = prod.lift (𝟙 Y) σ.hom := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, galoisTripleGraph]
    · simp only [Category.assoc, prod.lift_snd, galoisTripleGraph]
      rw [← Category.assoc, prod.lift_snd, prod.lift_fst]
  change F.obj.map (I.map (galoisTripleGraph Y σ τ)).op
    (F.obj.map (I.map prod.snd).op z -
      F.obj.map (I.map (prod.lift prod.fst (prod.snd ≫ prod.snd))).op z +
      F.obj.map (I.map (prod.lift prod.fst (prod.snd ≫ prod.fst))).op z) =
    F.obj.map (I.map (galoisTripleGraph Y σ τ)).op 0
  simp only [map_add, map_sub, map_zero, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, h₂₃, h₁₃, h₁₂]
  rw [I.map_comp, op_comp, F.obj.map_comp]
  change F.obj.map (I.map σ.hom).op
    (F.obj.map (I.map (prod.lift (𝟙 Y) τ.hom)).op z) -
      F.obj.map (I.map (prod.lift (𝟙 Y) (τ * σ).hom)).op z +
      F.obj.map (I.map (prod.lift (𝟙 Y) σ.hom)).op z = 0
  rw [hcoord, hcoord, hcoord, hc]
  abel

/-- Every actual deck cocycle with injective sheaf coefficients has an
actual section primitive on the Galois cover. -/
theorem exists_injective_galois_cocycle_primitive
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective F]
    (Y : FiniteEtale X) [IsGalois Y]
    (c : Aut Y → F.obj.obj (op ((finiteEtaleInclusion X).obj Y)))
    (hc : ∀ σ τ : Aut Y, c (τ * σ) =
      F.obj.map ((finiteEtaleInclusion X).map σ.hom).op (c τ) + c σ) :
    ∃ s : F.obj.obj (op ((finiteEtaleInclusion X).obj Y)),
      ∀ σ : Aut Y,
        F.obj.map ((finiteEtaleInclusion X).map σ.hom).op s - s = c σ := by
  let I := finiteEtaleInclusion X
  let z := (galoisSelfProductSectionsAddEquiv X F Y).symm c
  obtain ⟨s, hs⟩ := exists_injective_mappedProductSection_primitive
    X.smallEtaleTopology I Y F z (galoisCechSection_triangle X F Y c hc)
  refine ⟨s, ?_⟩
  intro σ
  have h := congrArg (F.obj.map (I.map (prod.lift (𝟙 Y) σ.hom)).op) hs
  simp only [map_sub, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, prod.lift_fst, prod.lift_snd] at h
  rw [I.map_id, op_id, F.obj.map_id] at h
  have hcoord : F.obj.map (I.map (prod.lift (𝟙 Y) σ.hom)).op z = c σ := by
    rw [← galoisSelfProductSectionsAddEquiv_apply]
    exact congrFun ((galoisSelfProductSectionsAddEquiv X F Y).apply_symm_apply c) σ
  exact h.trans hcoord

end EtaleCohomology
