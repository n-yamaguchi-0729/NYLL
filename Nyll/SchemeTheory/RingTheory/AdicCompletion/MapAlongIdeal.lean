/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.AdicCompletion.CompletionFromQuotientEquivalences
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Adic completion along an actual ideal-preserving ring map

The compatible maps on the original power quotients induce the completion
map. Evaluation proves its composition and identity laws. In particular,
local maps between Noetherian local rings induce local maps between their
maximal-adic completions, retaining the original ring and residue maps.
-/

@[expose] public section

noncomputable section

universe u v w

namespace AdicCompletion

variable {R : Type u} {S : Type v} {T : Type w}
  [CommRing R] [CommRing S] [CommRing T]

/-- The map on the original power quotients. -/
def quotientMapAlong (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (h : I ≤ J.comap f) (n : ℕ) : R ⧸ I ^ n →+* S ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f ((pow_le_pow_left' h n).trans (Ideal.le_comap_pow f n))

theorem quotientMapAlong_mk (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (h : I ≤ J.comap f) (n : ℕ) (r : R) :
    quotientMapAlong I J f h n (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk (J ^ n) (f r) :=
  Ideal.quotientMap_mk

private theorem quotientMapAlong_factorPow
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (h : I ≤ J.comap f)
    {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factorPow J hmn (quotientMapAlong I J f h n x) =
      quotientMapAlong I J f h m (Ideal.Quotient.factorPow I hmn x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientMapAlong_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, quotientMapAlong_mk]

/-- The actual completion map induced by a map preserving the adic ideals. -/
def mapAlong (I : Ideal R) (J : Ideal S) (f : R →+* S) (h : I ≤ J.comap f) :
    AdicCompletion I R →+* AdicCompletion J S :=
  liftRingHom J
    (fun n => (quotientMapAlong I J f h n).comp (evalₐ I n).toRingHom)
    (by
      intro m n hmn
      apply RingHom.ext
      intro x
      change Ideal.Quotient.factorPow J hmn
          (quotientMapAlong I J f h n (evalₐ I n x)) =
        quotientMapAlong I J f h m (evalₐ I m x)
      rw [quotientMapAlong_factorPow, factorPow_evalRing])

theorem eval_mapAlong (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (h : I ≤ J.comap f) (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (mapAlong I J f h x) = quotientMapAlong I J f h n (evalₐ I n x) := by
  unfold mapAlong
  apply evalₐ_liftRingHom
  intro m n hmn
  apply RingHom.ext
  intro y
  change Ideal.Quotient.factorPow J hmn
      (quotientMapAlong I J f h n (evalₐ I n y)) =
    quotientMapAlong I J f h m (evalₐ I m y)
  rw [quotientMapAlong_factorPow, factorPow_evalRing]

/-- The completion map retains the original ring map on every original element. -/
theorem mapAlong_algebraMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (h : I ≤ J.comap f) (r : R) :
    mapAlong I J f h (algebraMap R (AdicCompletion I R) r) =
      algebraMap S (AdicCompletion J S) (f r) := by
  apply ext_evalₐ
  intro n
  change evalₐ J n (mapAlong I J f h (of I R r)) = evalₐ J n (of J S (f r))
  rw [eval_mapAlong, evalₐ_of, quotientMapAlong_mk, evalₐ_of]

theorem mapAlong_comp_algebraMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (h : I ≤ J.comap f) :
    (mapAlong I J f h).comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f :=
  RingHom.ext (mapAlong_algebraMap I J f h)

/-- An ideal is contained in its inverse image under the identity homomorphism. -/
theorem le_comap_id (I : Ideal R) : I ≤ I.comap (RingHom.id R) := by
  intro r hr
  exact hr

/-- Compatibility of ideals with ring homomorphisms is preserved under composition. -/
theorem le_comap_comp (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (f : R →+* S) (g : S →+* T) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    I ≤ K.comap (g.comp f) := by
  intro r hr
  exact hg (hf hr)

theorem mapAlong_id (I : Ideal R) :
    mapAlong I I (RingHom.id R) (le_comap_id I) =
      RingHom.id (AdicCompletion I R) := by
  apply RingHom.ext
  intro x
  apply ext_evalₐ
  intro n
  rw [eval_mapAlong, RingHom.id_apply]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  rw [← hr, quotientMapAlong_mk, RingHom.id_apply]

theorem mapAlong_comp (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (f : R →+* S) (g : S →+* T) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    (mapAlong J K g hg).comp (mapAlong I J f hf) =
      mapAlong I K (g.comp f) (le_comap_comp I J K f g hf hg) := by
  apply RingHom.ext
  intro x
  apply ext_evalₐ
  intro n
  rw [RingHom.comp_apply, eval_mapAlong, eval_mapAlong, eval_mapAlong]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  rw [← hr, quotientMapAlong_mk, quotientMapAlong_mk, quotientMapAlong_mk,
    RingHom.comp_apply]

theorem evalOne_mapAlong (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (h : I ≤ J.comap f) (x : AdicCompletion I R) :
    evalOneₐ J (mapAlong I J f h x) = Ideal.quotientMap J f h (evalOneₐ I x) := by
  rw [← factorₐ_evalₐ_one, ← factorₐ_evalₐ_one I x]
  rw [eval_mapAlong]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I 1 x)
  rw [← hr, quotientMapAlong_mk, Ideal.Quotient.factor_mk,
    Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]

section Local

variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]

/-- A local ring map induces its actual map of maximal-adic completions. -/
def mapMaximal (f : R →+* S) [IsLocalHom f] :
    AdicCompletion (IsLocalRing.maximalIdeal R) R →+*
      AdicCompletion (IsLocalRing.maximalIdeal S) S :=
  mapAlong _ _ f (IsLocalRing.maximalIdeal_comap f).symm.le

theorem mapMaximal_algebraMap (f : R →+* S) [IsLocalHom f] (r : R) :
    mapMaximal f (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
      algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (f r) :=
  mapAlong_algebraMap _ _ f _ r

theorem mapMaximal_id : mapMaximal (RingHom.id R) =
    RingHom.id (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  mapAlong_id _

theorem mapMaximal_comp (f : R →+* S) (g : S →+* T)
    [IsLocalHom f] [IsLocalHom g] :
    (mapMaximal g).comp (mapMaximal f) = mapMaximal (g.comp f) :=
  mapAlong_comp _ _ _ f g _ _

theorem evalOne_mapMaximal (f : R →+* S) [IsLocalHom f]
    (x : AdicCompletion (IsLocalRing.maximalIdeal R) R) :
    evalOneₐ (IsLocalRing.maximalIdeal S) (mapMaximal f x) =
      IsLocalRing.ResidueField.map f (evalOneₐ (IsLocalRing.maximalIdeal R) x) :=
  evalOne_mapAlong _ _ f _ x

/-- Localness follows from the computed image of the original maximal ideal. -/
instance mapMaximal_isLocalHom [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f] : IsLocalHom (mapMaximal f) := by
  apply ((IsLocalRing.local_hom_TFAE (mapMaximal f)).out 3 1).mp
  rw [maximalIdeal_eq_map (R := R), maximalIdeal_eq_map (R := S), Ideal.map_map]
  have hcomp := mapAlong_comp_algebraMap (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal S) f (IsLocalRing.maximalIdeal_comap f).symm.le
  change (IsLocalRing.maximalIdeal R).map
    ((mapAlong _ _ f _).comp (algebraMap R (AdicCompletion _ R))) ≤ _
  rw [hcomp, ← Ideal.map_map]
  exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le f)

end Local

end AdicCompletion
