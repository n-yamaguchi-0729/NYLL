/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafCohomologyIso
import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafPushforwardCech
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Modules.Functoriality.BaseChangeHom
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Native Čech cohomology along a scheme isomorphism

Pushforward along the actual scheme isomorphism is an equivalence.
Consequently, the original pullback adjunction unit is an isomorphism.
Its maps on sections, followed by the direct-image cochain comparison,
identify the original Čech cohomology with that of the pulled back
native sheaf on the preimage cover.

The computation lemmas retain the original adjunction unit. In
particular, the comparison can transport Serre vanishing across the
canonical scheme isomorphism for projective-space base change.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private def schemeIsoPullbackUnitIso {X Y : Scheme.{u}} (e : Y ≅ X) (M : X.Modules) :
    M ≅ (pushforward e.hom).obj ((pullback e.hom).obj M) := by
  have : (pushforward e.hom).IsEquivalence :=
    (pushforwardIsoEquivalence e).isEquivalence_functor
  exact asIso ((pullbackPushforwardAdjunction e.hom).unit.app M)

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [IsSeparated f] (e : Y ≅ X)
  (M : X.Modules) (K : X.OrderedAffineCover)

/-- Cochains of the pulled-back sheaf are obtained from the original
adjunction unit and the original preimage-cover restriction maps. -/
def pullbackCochainEquivOfSchemeIso (q : ℕ) :
    (toOModulePresheaf f M).cochain K q ≃ₗ[R]
      (toOModulePresheaf (e.hom ≫ f) ((pullback e.hom).obj M)).cochain
        (K.preimage e.hom) q :=
  (cochainEquivOfIso f K (schemeIsoPullbackUnitIso e M) q).trans
    (pushforwardCochainEquiv f e.hom ((pullback e.hom).obj M) K q).symm

/-- After the literal preimage-cover comparison, the cochain map is
the original adjunction unit on every original cover intersection. -/
theorem pullbackCochainEquivOfSchemeIso_pushforward (q : ℕ)
    (x : (toOModulePresheaf f M).cochain K q) (s : K.Idx q) :
    pushforwardCochainEquiv f e.hom ((pullback e.hom).obj M) K q
        (pullbackCochainEquivOfSchemeIso f e M K q x) s =
      (((pullbackPushforwardAdjunction e.hom).unit.app M).app (K.inter s)) (x s) := by
  exact congrFun
    ((pushforwardCochainEquiv f e.hom ((pullback e.hom).obj M) K q).apply_symm_apply
      (cochainEquivOfIso f K (schemeIsoPullbackUnitIso e M) q x)) s

/-- The native pullback along a scheme isomorphism preserves the actual
positive Čech cohomology on the original and preimage covers. -/
def pullbackHSuccEquivOfSchemeIso (q : ℕ) :
    (toOModulePresheaf f M).HSucc K q ≃ₗ[R]
      (toOModulePresheaf (e.hom ≫ f) ((pullback e.hom).obj M)).HSucc
        (K.preimage e.hom) q :=
  (HSuccEquivOfIso f K (schemeIsoPullbackUnitIso e M) q).trans
    (pushforwardHSuccEquiv f e.hom ((pullback e.hom).obj M) K q).symm

/-- The induced cohomology map is compatible with the original map
of the adjunction unit, including its actual map on cocycle classes. -/
theorem pullbackHSuccEquivOfSchemeIso_pushforward (q : ℕ)
    (x : (toOModulePresheaf f M).HSucc K q) :
    pushforwardHSuccEquiv f e.hom ((pullback e.hom).obj M) K q
        (pullbackHSuccEquivOfSchemeIso f e M K q x) =
      (toOModulePresheafHom f
        ((pullbackPushforwardAdjunction e.hom).unit.app M)).toAffHom.HSuccMap K q x :=
  (pushforwardHSuccEquiv f e.hom ((pullback e.hom).obj M) K q).apply_symm_apply
    (HSuccEquivOfIso f K (schemeIsoPullbackUnitIso e M) q x)

/-- Vanishing on the actual preimage cover descends along the scheme
isomorphism through the constructed cohomology equivalence. -/
theorem subsingleton_HSucc_of_schemeIso_pullback (q : ℕ)
    [Subsingleton ((toOModulePresheaf (e.hom ≫ f) ((pullback e.hom).obj M)).HSucc
      (K.preimage e.hom) q)] : Subsingleton ((toOModulePresheaf f M).HSucc K q) :=
  ⟨fun x y => (pullbackHSuccEquivOfSchemeIso f e M K q).injective
    (Subsingleton.elim (pullbackHSuccEquivOfSchemeIso f e M K q x)
      (pullbackHSuccEquivOfSchemeIso f e M K q y))⟩

end AlgebraicGeometry.Scheme.Modules
