/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompleteClosedFiberFundamentalGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceBasePointComparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition

/-!
# Composition through two proper complete-local models

Specializing first to the closed fiber of one complete-local model and then
to that of another agrees with direct specialization. The intervening map
is an actual morphism of total spaces, and the direct path is constructed
by pushing forward the first path and composing with the second.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

private theorem conjAut_eqToIso_point_eq
    {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {x y : Spec (CommRingCat.of Ω) ⟶ X} (h : x = y) (b : π₁ᵉᵗ(x)) :
    (eqToIso (congrArg fiber h)).conjAut b = h ▸ b := by
  subst y
  rfl

/-- Two successive specializations through actual complete-local models
compose for the explicitly induced path on the terminal total space.
Both closed-fiber comparisons come from properness and completeness. -/
theorem properCompleteSpecializationHom_comp
    (R A : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (g : Y ⟶ Spec (CommRingCat.of A)) [IsProper g]
    (q : Y ⟶ X) {T : Scheme.{u}} (j : T ⟶ Y)
    {Ω Ωₘ Ωₛ : Type u} [Field Ω] [Field Ωₘ] [Field Ωₛ]
    (xi : Spec (CommRingCat.of Ω) ⟶ T)
    (ym : Spec (CommRingCat.of Ωₘ) ⟶
      Limits.pullback g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (xs : Spec (CommRingCat.of Ωₛ) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (t₁ : fiber (xi ≫ j) ≅ fiber (ym ≫
      Limits.pullback.fst g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))))
    (t₂ : fiber (ym ≫
        (Limits.pullback.fst g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ q)) ≅
      fiber (xs ≫
        Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))
    (b : π₁ᵉᵗ(xi)) :
    let pY := Limits.pullback.fst g
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
    let hsource : (xi ≫ j) ≫ q = xi ≫ (j ≫ q) := Category.assoc xi j q
    let hmiddle : (ym ≫ pY) ≫ q = ym ≫ (pY ≫ q) := Category.assoc ym pY q
    let tq : fiber ((xi ≫ j) ≫ q) ≅ fiber ((ym ≫ pY) ≫ q) :=
      (pullbackFiberIso q (xi ≫ j)).symm ≪≫
        Functor.isoWhiskerLeft (pullback q) t₁ ≪≫ pullbackFiberIso q (ym ≫ pY)
    let tcomp : fiber (xi ≫ (j ≫ q)) ≅ fiber (xs ≫
        Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :=
      (eqToIso (congrArg fiber hsource)).symm ≪≫ tq ≪≫
        eqToIso (congrArg fiber hmiddle) ≪≫ t₂
    properCompleteSpecializationHom R f (pY ≫ q) ym xs t₂
        (properCompleteSpecializationHom A g j xi ym t₁ b) =
      properCompleteSpecializationHom R f (j ≫ q) xi xs tcomp b := by
  intro pY hsource hmiddle tq tcomp
  let csource := eqToIso (congrArg fiber hsource)
  let cmiddle := eqToIso (congrArg fiber hmiddle)
  let s₁ : π₁ᵉᵗ(ym) := properCompleteSpecializationHom A g j xi ym t₁ b
  let e := fundamentalGroupEquivProperCompleteClosedFiber R f xs
  have hfirst : fundamentalGroupHom pY ym s₁ =
      t₁.conjAut (fundamentalGroupHom j xi b) :=
    properCompleteSpecializationHom_triangle A g j xi ym t₁ b
  have hsource_map : csource.conjAut
      (fundamentalGroupHom q (xi ≫ j) (fundamentalGroupHom j xi b)) =
        fundamentalGroupHom (j ≫ q) xi b := by
    change (eqToIso (congrArg fiber hsource)).conjAut _ = _
    rw [conjAut_eqToIso_point_eq hsource]
    exact fundamentalGroupHom_comp_of_eq j q (j ≫ q) rfl xi hsource b
  have hmiddle_map (c : π₁ᵉᵗ(ym)) : cmiddle.conjAut
      (fundamentalGroupHom q (ym ≫ pY) (fundamentalGroupHom pY ym c)) =
        fundamentalGroupHom (pY ≫ q) ym c := by
    change (eqToIso (congrArg fiber hmiddle)).conjAut _ = _
    rw [conjAut_eqToIso_point_eq hmiddle]
    exact fundamentalGroupHom_comp_of_eq pY q (pY ≫ q) rfl ym hmiddle c
  have hsource_inv : csource.symm.conjAut (fundamentalGroupHom (j ≫ q) xi b) =
      fundamentalGroupHom q (xi ≫ j) (fundamentalGroupHom j xi b) := by
    rw [← hsource_map, ← Iso.trans_conjAut, Iso.self_symm_id]
    rfl
  have hpath : tcomp.conjAut (fundamentalGroupHom (j ≫ q) xi b) =
      t₂.conjAut (cmiddle.conjAut (tq.conjAut
        (fundamentalGroupHom q (xi ≫ j) (fundamentalGroupHom j xi b)))) := by
    change (csource.symm ≪≫ tq ≪≫ cmiddle ≪≫ t₂).conjAut _ = _
    simp only [Iso.trans_conjAut, hsource_inv]
  apply e.injective
  calc
    _ = t₂.conjAut (fundamentalGroupHom (pY ≫ q) ym s₁) :=
      properCompleteSpecializationHom_triangle R f (pY ≫ q) ym xs t₂ s₁
    _ = t₂.conjAut (cmiddle.conjAut
        (fundamentalGroupHom q (ym ≫ pY) (fundamentalGroupHom pY ym s₁))) :=
      congrArg t₂.conjAut (hmiddle_map s₁).symm
    _ = t₂.conjAut (cmiddle.conjAut (fundamentalGroupHom q (ym ≫ pY)
        (t₁.conjAut (fundamentalGroupHom j xi b)))) :=
      congrArg (fun c => t₂.conjAut (cmiddle.conjAut
        (fundamentalGroupHom q (ym ≫ pY) c))) hfirst
    _ = t₂.conjAut (cmiddle.conjAut (tq.conjAut
        (fundamentalGroupHom q (xi ≫ j) (fundamentalGroupHom j xi b)))) :=
      congrArg (fun c => t₂.conjAut (cmiddle.conjAut c))
        (fundamentalGroupHom_conjAut q (xi ≫ j) (ym ≫ pY) t₁
          (fundamentalGroupHom j xi b)).symm
    _ = tcomp.conjAut (fundamentalGroupHom (j ≫ q) xi b) := hpath.symm
    _ = _ := (properCompleteSpecializationHom_triangle R f (j ≫ q) xi xs tcomp b).symm

end AlgebraicGeometry.FiniteEtale
