/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Galois.Topology

/-!
# Automorphism groups under an equivalence of categories

Precomposition by an equivalence is fully faithful on functor categories.
Consequently the actual continuous homomorphism on automorphism groups is
bijective. The automorphism group of every finite-set-valued functor is compact
Hausdorff, so the inverse is continuous as well. No connectedness or Galois
category assumptions are needed for this argument.
-/

noncomputable section

open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

universe u₁ u₂ v₁ v₂ w

variable {C : Type u₁} [Category.{u₂} C]
  {C' : Type v₁} [Category.{v₂} C']

/-- The canonical automorphism homomorphism is bijective under an equivalence. -/
theorem autHomOfCompIso_bijective_of_isEquivalence
    (H : C ⥤ C') [H.IsEquivalence] {F : C ⥤ FintypeCat.{w}}
    {F' : C' ⥤ FintypeCat.{w}} (t : H ⋙ F' ≅ F) :
    Function.Bijective (autHomOfCompIso H t) := by
  let W : (C' ⥤ FintypeCat.{w}) ⥤ (C ⥤ FintypeCat.{w}) :=
    (Functor.whiskeringLeft C C' FintypeCat.{w}).obj H
  let e : Aut F' ≃* Aut (H ⋙ F') :=
    (Functor.FullyFaithful.ofFullyFaithful W).autMulEquivOfFullyFaithful F'
  change Function.Bijective (fun a : Aut F' => t.conjAut (e a))
  exact t.conjAut.bijective.comp e.bijective

/-- The canonical homomorphism, upgraded to a topological group isomorphism. -/
def autEquivOfCompIsoOfEquivalence
    (H : C ⥤ C') [H.IsEquivalence] {F : C ⥤ FintypeCat.{w}}
    {F' : C' ⥤ FintypeCat.{w}} (t : H ⋙ F' ≅ F) :
    Aut F' ≃ₜ* Aut F :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (autHomOfCompIso H t).toMonoidHom (autHomOfCompIso H t).continuous_toFun
    (autHomOfCompIso_bijective_of_isEquivalence H t)

/-- The isomorphism retains the original forward map. -/
theorem autEquivOfCompIsoOfEquivalence_apply
    (H : C ⥤ C') [H.IsEquivalence] {F : C ⥤ FintypeCat.{w}}
    {F' : C' ⥤ FintypeCat.{w}} (t : H ⋙ F' ≅ F) (a : Aut F') :
    autEquivOfCompIsoOfEquivalence H t a = autHomOfCompIso H t a := rfl

end CategoryTheory.PreGaloisCategory
