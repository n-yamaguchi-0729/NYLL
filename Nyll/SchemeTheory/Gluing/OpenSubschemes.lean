/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
# Gluing and extending open subschemes

Open-immersion gluing and extension of morphisms from a stalk to an open neighborhood.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties
namespace NOSProofs
namespace Reduction_Support_Schemes_SchemeExistsGlueForallIsOpenImmersionOfForallIsOpenImmersion


universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace E86WPS

theorem some_hom_eq {J : Type u} {k i : J}
    (a : WidePushoutShape.Hom (some k) (some i)) : k = i := by
  match a with
  | .id _ => rfl

end E86WPS

theorem _root_.AlgebraicGeometry.Scheme.exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion
    (W : Scheme.{u}) {ι : Type u} [Nonempty ι] (U : ι → Scheme.{u}) (f : ∀ i, W ⟶ U i)
    [∀ i, IsOpenImmersion (f i)] :
    ∃ (Y : Scheme.{u}) (g : ∀ i, U i ⟶ Y),
      (∀ i, IsOpenImmersion (g i)) ∧
      (∀ i j, f i ≫ g i = f j ≫ g j) ∧
      (⋃ i, Set.range (g i).base = Set.univ) ∧
      (∀ i j, i ≠ j → Set.range (g i).base ∩ Set.range (g j).base = Set.range (f i ≫ g i).base) ∧
      (∀ (Z : Scheme.{u}) (h : ∀ i, U i ⟶ Z), (∀ i j, f i ≫ h i = f j ≫ h j) →
        ∃! k : Y ⟶ Z, ∀ i, g i ≫ k = h i) := by
  classical
  let F : WidePushoutShape ι ⥤ Scheme.{u} := WidePushoutShape.wideSpan W U f
  have hF : ∀ {i j : WidePushoutShape ι} (a : i ⟶ j), IsOpenImmersion (F.map a) := by
    rintro i j ⟨⟩
    · exact inferInstanceAs (IsOpenImmersion (𝟙 _))
    · exact inferInstanceAs (IsOpenImmersion (f _))
  let Y : Scheme.{u} := colimit F
  let g : ∀ i, U i ⟶ Y := fun i => colimit.ι F (some i)
  have hgW : ∀ i, f i ≫ g i = colimit.ι F none := fun i => colimit.w F (WidePushoutShape.Hom.init i)
  refine ⟨Y, g, fun i => inferInstanceAs (IsOpenImmersion (colimit.ι F (some i))), ?_, ?_, ?_, ?_⟩
  · intro i j; rw [hgW, hgW]
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨(_ | i), x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F y
    · obtain ⟨i⟩ := ‹Nonempty ι›
      refine Set.mem_iUnion.mpr ⟨i, (f i).base x, ?_⟩
      rw [← Scheme.Hom.comp_apply, hgW]; exact hx
    · exact Set.mem_iUnion.mpr ⟨i, x, hx⟩
  · intro i j hij
    ext y; constructor
    · rintro ⟨⟨xi, rfl⟩, ⟨xj, hxj⟩⟩
      obtain ⟨k, fi, fj, x, hfi, hfj⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp hxj.symm
      rcases k with (_ | k)
      · obtain rfl : fi = WidePushoutShape.Hom.init i := Subsingleton.elim _ _
        refine ⟨x, ?_⟩
        rw [Scheme.Hom.comp_apply]
        exact congrArg (g i).base hfi
      · exact absurd ((E86WPS.some_hom_eq fi).symm.trans (E86WPS.some_hom_eq fj)) hij
    · rintro ⟨w, rfl⟩
      refine ⟨⟨(f i).base w, by rw [← Scheme.Hom.comp_apply]⟩, ⟨(f j).base w, ?_⟩⟩
      rw [← Scheme.Hom.comp_apply, hgW, hgW]
  · intro Z h hh
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    let c : Cocone F := WidePushoutShape.mkCocone (f i₀ ≫ h i₀) h (fun i => hh i i₀)
    refine ⟨colimit.desc F c, fun i => colimit.ι_desc c (some i), ?_⟩
    intro k hk
    apply colimit.hom_ext
    intro j
    erw [colimit.ι_desc]
    rcases j with (_ | i)
    · change colimit.ι F none ≫ k = f i₀ ≫ h i₀
      rw [← hgW i₀]
      exact (Category.assoc _ _ _).trans (congrArg (fun t => f i₀ ≫ t) (hk i₀))
    · exact hk i

end Reduction_Support_Schemes_SchemeExistsGlueForallIsOpenImmersionOfForallIsOpenImmersion
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties
namespace NOSProofs
namespace Reduction_Support_Schemes_SchemeExistsOpensExtensionOfFromSpecStalk


universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem _root_.AlgebraicGeometry.Scheme.exists_opens_extension_of_fromSpecStalk
    {S G H : Scheme.{u}} (sG : G ⟶ S) (sH : H ⟶ S) [LocallyOfFiniteType sH]
    (η : G) [G.IsGermInjectiveAt η]
    (w : Spec (G.presheaf.stalk η) ⟶ H) (hw : w ≫ sH = G.fromSpecStalk η ≫ sG) :
    ∃ (U : G.Opens) (hη : η ∈ U) (v : (U : Scheme.{u}) ⟶ H),
      v ≫ sH = U.ι ≫ sG ∧ U.fromSpecStalkOfMem η hη ≫ v = w := by
  obtain ⟨U, hη, v, h1, h2⟩ := spread_out_of_isGermInjective' sG sH w hw
  exact ⟨U, hη, v, h2, h1.symm⟩

end Reduction_Support_Schemes_SchemeExistsOpensExtensionOfFromSpecStalk
end NOSProofs
end AbelianVarieties
end
