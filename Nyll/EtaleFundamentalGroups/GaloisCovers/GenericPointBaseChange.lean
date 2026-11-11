/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.FiniteSeparable
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect
public import Mathlib.FieldTheory.IsSepClosed

/-!
# A compatible geometric point over the actual structural constants

The structure morphism supplies the function field's constant algebra. Its
chosen embedding into the original generic field then supplies the constant
algebra on that field. A separable constant closure embeds over this actual
algebra, giving a point of the literal geometric base change with both
projection identities. This does not assume compatibility of an older
constant embedding with a newly selected finite constant cover.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace EtaleFundamentalGroups

universe u

/-- Construct a compatible constant embedding and geometric base-change
point without changing the original generic field or generic point. -/
theorem exists_genericPoint_geometricBaseChange
    (k κ Ω : Type u) [Field k] [Field κ] [Field Ω]
    [Algebra k κ] [IsSepClosure k κ] [IsSepClosed Ω]
    {U : Scheme.{u}} [IsIntegral U] [Algebra U.functionField Ω]
    (f : U ⟶ Spec (.of k)) :
    let : Algebra k U.functionField := stalkAlgebra f (genericPoint U)
    let : Algebra k Ω :=
      ((algebraMap U.functionField Ω).comp (algebraMap k U.functionField)).toAlgebra
    ∃ (a : κ →ₐ[k] Ω)
      (xi : Spec (.of Ω) ⟶ pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f),
      xi ≫ pullback.snd _ f = U.genericExtensionMorphism Ω ∧
      xi ≫ pullback.fst _ f = Spec.map (CommRingCat.ofHom a.toRingHom) := by
  intro instkF instkΩ
  let a : κ →ₐ[k] Ω := IsSepClosed.lift (K := k) (L := κ) (M := Ω)
  have hbase : U.fromSpecStalk (genericPoint U) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k U.functionField)) :=
    fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra f (genericPoint U)
  have hp : U.genericExtensionMorphism Ω ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
    change (Spec.map (CommRingCat.ofHom (algebraMap U.functionField Ω)) ≫
      U.fromSpecStalk (genericPoint U)) ≫ f = _
    rw [Category.assoc, hbase, ← Spec.map_comp]
    rfl
  have hs : Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k κ)) =
        U.genericExtensionMorphism Ω ≫ f := by
    rw [hp, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (a.toRingHom.comp (algebraMap k κ))) = _
    have ha : a.toRingHom.comp (algebraMap k κ) = algebraMap k Ω := by
      ext x
      exact a.commutes x
    exact congrArg (fun g : k →+* Ω => Spec.map (CommRingCat.ofHom g)) ha
  exact ⟨a, pullback.lift (Spec.map (CommRingCat.ofHom a.toRingHom))
    (U.genericExtensionMorphism Ω) hs, pullback.lift_snd _ _ hs,
    pullback.lift_fst _ _ hs⟩

end EtaleFundamentalGroups
