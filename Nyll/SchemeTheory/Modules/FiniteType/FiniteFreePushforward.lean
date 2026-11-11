/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeTransport
public import Nyll.SchemeTheory.Modules.Functoriality.LocallyFreePushforwardFinite
public import Nyll.SchemeTheory.Modules.Functoriality.PushforwardRestrict
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Finite local bases for finite flat direct-image algebras

The locally constant rank function separates the base into opens of
constant rank. The existing native finite-flat trivializations apply on
each such open and cover the original direct image, allowing varying rank.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite flat morphism of finite presentation has a finite locally
free original direct-image structure module; its rank may vary. -/
theorem finiteFreeLocus_pushforward_unit_eq_top
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsFinite q] [Flat q]
    [LocallyOfFinitePresentation q] :
    finiteFreeLocus ((pushforward q).obj (𝟙_ X.Modules)) = ⊤ := by
  let P : Y.Modules := (pushforward q).obj (𝟙_ X.Modules)
  apply top_unique
  intro y _
  let W : Y.Opens :=
    ⟨{z | q.finrank z = q.finrank y}, q.isLocallyConstant_finrank.isOpen_fiber _⟩
  have hyW : y ∈ W := rfl
  let g := q ∣_ W
  have hn : ∀ z : W.toScheme, g.finrank z = q.finrank y := by
    intro z
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict q W).flip]
    exact z.property
  have hfree : IsLocallyFreeOfRank (q.finrank y)
      ((pushforward g).obj (𝟙_ (q ⁻¹ᵁ W).toScheme.Modules)) :=
    isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
      g (q.finrank y) hn (𝟙_ (q ⁻¹ᵁ W).toScheme.Modules)
      (fun z => ⟨⊤, trivial, ⟨pullbackTensorUnitObjIso (g ⁻¹ᵁ ⊤).ι⟩⟩)
  let e : (pushforward g).obj (𝟙_ (q ⁻¹ᵁ W).toScheme.Modules) ≅ P.restrict W.ι :=
    (pushforward g).mapIso (restrictUnitIso (q ⁻¹ᵁ W).ι).symm ≪≫
      (pushforwardRestrictIso q W).app (𝟙_ X.Modules)
  have hP : finiteFreeLocus (P.restrict W.ι) = ⊤ :=
    (finiteFreeLocus_eq_of_iso e).symm.trans
      (finiteFreeLocus_eq_top_of_isLocallyFreeOfRank _ hfree)
  exact le_finiteFreeLocus_of_restrict_eq_top P W hP hyW

end AlgebraicGeometry.Scheme.Modules
