/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionHom

/-!
# Open range containment descends below a coefficient stage

If the limit base change of a quasi-compact relative model maps into a
specified open of that model, a later coefficient base change already
maps into that open. The existing actual limit is reindexed below the
chosen coefficient stage using `Over.conePost`; no new limit or change
of strict henselization is assumed. Affine coefficient transitions and
quasi-compactness suffice.
-/

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineTransitionHom

universe u

/-- Open range containment of a relative model's actual limit base change
is witnessed below its original coefficient stage. -/
theorem exists_range_subset_later_stage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : I, CompactSpace (D.obj i)]
    (i : I) {Y : Scheme.{u}} (f : Y ⟶ D.obj i) [QuasiCompact f]
    (W : Y.Opens)
    (hW : Set.range (pullback.snd (c.π.app i) f) ⊆ W.carrier) :
    ∃ (j : I) (a : j ⟶ i),
      Set.range (pullback.snd (D.map a) f) ⊆ W.carrier := by
  let E : Over i ⥤ Over (D.obj i) := Over.post D
  let s : Cone E := (Over.conePost D i).obj c
  have hs : IsLimit s := Over.isLimitConePost i hc
  have : ∀ {j k : Over i} (a : j ⟶ k), IsAffineHom (E.map a).left :=
    fun a => inferInstanceAs (IsAffineHom (D.map a.left))
  have : ∀ j : Over i, CompactSpace (E.obj j).left :=
    fun j => inferInstanceAs (CompactSpace (D.obj j.left))
  have : ∀ {j k : Over i} (a : j ⟶ k), IsAffineHom ((diagram E f).map a) :=
    fun a => diagram_map_isAffineHom E f a
  have : ∀ j : Over i, CompactSpace ((diagram E f).obj j) :=
    diagram_obj_compactSpace E f
  let i₀ : Over i := Over.mk (𝟙 i)
  let p₀ : (diagram E f).obj i₀ ⟶ Y := pullback.snd (E.obj i₀).hom f
  let W₀ : ((diagram E f).obj i₀).Opens := p₀ ⁻¹ᵁ W
  have htop : (cone E s f).π.app i₀ ⁻¹ᵁ W₀ = ⊤ := by
    change (cone E s f).π.app i₀ ⁻¹ᵁ (pullback.snd (E.obj i₀).hom f ⁻¹ᵁ W) = ⊤
    rw [← Scheme.Hom.comp_preimage, cone_map_snd]
    apply top_unique
    intro z _
    exact hW ⟨z, rfl⟩
  obtain ⟨j, a, ha⟩ := exists_map_eq_top (diagram E f) (cone E s f)
    (coneIsLimit E s hs f) W₀ htop
  refine ⟨j.left, j.hom, ?_⟩
  rintro y ⟨z, rfl⟩
  have hz : (diagram E f).map a z ∈ W₀ := ha.ge (Set.mem_univ z)
  have hp : (diagram E f).map a ≫ p₀ = pullback.snd (E.obj j).hom f :=
    Over.w ((Over.pullback f).map (E.map a))
  have hpoint : p₀ ((diagram E f).map a z) = pullback.snd (E.obj j).hom f z :=
    (Scheme.Hom.comp_apply ((diagram E f).map a) p₀ z).symm.trans
      (congrArg (fun t : (diagram E f).obj j ⟶ Y => t z) hp)
  change p₀ ((diagram E f).map a z) ∈ W at hz
  exact hpoint ▸ hz

end AlgebraicGeometry.AffineTransitionHom
