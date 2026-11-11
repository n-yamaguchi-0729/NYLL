/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselizationUniversal
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkPuncture
public import Nyll.SchemeTheory.RingTheory.Henselian.ModuleFinite
public import Nyll.SchemeTheory.RingTheory.Henselian.HenselianNilIdeal
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Quotients of the actual ordinary henselization

If a quotient of a local ring is already henselian, its canonical map
to the corresponding quotient of the constructed ordinary henselization
is an isomorphism. Both inverse identities follow from the actual
universal local map, rather than from a new henselization package.

This is a finite-level ingredient for comparing the original adic
completion with the completion of its henselization. It does not assert
Artin approximation or the regularity of a completion map.
-/

@[expose] public section

noncomputable section

universe u

namespace EtaleFundamentalGroups.StrictHenselian

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A quotient that is already henselian is unchanged by first taking
the actual ordinary henselization of the original local ring. -/
theorem ordinaryHenselization_quotientMap_bijective
    (I : Ideal R) [HenselianLocalRing (R ⧸ I)] :
    Function.Bijective
      (Ideal.quotientMap (I.map (ordinaryHenselizationMap R))
        (ordinaryHenselizationMap R) Ideal.le_comap_map) := by
  let H := ordinaryHenselization R
  let j : R →+* H := ordinaryHenselizationMap R
  let J : Ideal H := I.map j
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hJ : J ≠ ⊤ :=
    (lt_of_le_of_lt (Ideal.map_mono (IsLocalRing.le_maximalIdeal hI))
      (IsLocalRing.map_maximalIdeal_lt_top j)).ne
  have : Nontrivial (H ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (H ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : HenselianLocalRing (H ⧸ J) :=
    HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := H) (S := H ⧸ J)
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let l : H →+* R ⧸ I := ordinaryHenselizationLift (Ideal.Quotient.mk I)
  have hl : l.comp j = Ideal.Quotient.mk I :=
    ordinaryHenselizationLift_comp_map (Ideal.Quotient.mk I)
  have hlJ : J ≤ RingHom.ker l := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change l (j a) = 0
    exact (RingHom.congr_fun hl a).trans (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  let p : H ⧸ J →+* R ⧸ I :=
    Ideal.Quotient.lift J l (fun a ha => RingHom.mem_ker.mp (hlJ ha))
  let q : R ⧸ I →+* H ⧸ J := Ideal.quotientMap J j Ideal.le_comap_map
  have hpq : p.comp q = RingHom.id (R ⧸ I) := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro a
    exact RingHom.congr_fun hl a
  have : IsLocalHom q := by
    constructor
    intro a ha
    have hunit := ha.map p
    change IsUnit ((p.comp q) a) at hunit
    rw [RingHom.congr_fun hpq a] at hunit
    exact hunit
  have hg : (q.comp l).comp j = (Ideal.Quotient.mk J).comp j := by
    rw [RingHom.comp_assoc, hl]
    rfl
  have heq : q.comp l = Ideal.Quotient.mk J :=
    (ordinaryHenselizationLift_unique ((Ideal.Quotient.mk J).comp j)
      (q.comp l) hg).trans
      (ordinaryHenselizationLift_unique ((Ideal.Quotient.mk J).comp j)
        (Ideal.Quotient.mk J) rfl).symm
  change Function.Bijective q
  constructor
  · intro a b hab
    have hp := congrArg p hab
    exact (RingHom.congr_fun hpq a).symm.trans
      (hp.trans (RingHom.congr_fun hpq b))
  · intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨l a, RingHom.congr_fun heq a⟩

/-- The canonical quotient comparison with its literal original map. -/
def ordinaryHenselizationQuotientEquiv
    (I : Ideal R) [HenselianLocalRing (R ⧸ I)] :
    R ⧸ I ≃+* ordinaryHenselization R ⧸ I.map (ordinaryHenselizationMap R) :=
  RingEquiv.ofBijective
    (Ideal.quotientMap (I.map (ordinaryHenselizationMap R))
      (ordinaryHenselizationMap R) Ideal.le_comap_map)
    (ordinaryHenselization_quotientMap_bijective R I)

/-- The finite-level isomorphism preserves the original quotient maps. -/
theorem ordinaryHenselizationQuotientEquiv_mk
    (I : Ideal R) [HenselianLocalRing (R ⧸ I)] (a : R) :
    ordinaryHenselizationQuotientEquiv R I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (ordinaryHenselizationMap R))
        (ordinaryHenselizationMap R a) :=
  rfl

/-- Every positive infinitesimal quotient of the original local ring is
henselian, using the existing nil-ideal Hensel theorem. No Noetherianity
or henselianity of the original local ring is required. -/
theorem henselianLocalRing_quotient_maximalIdeal_pow (n : ℕ) :
    HenselianLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)) := by
  let I : Ideal R := IsLocalRing.maximalIdeal R ^ (n + 1)
  let Q := R ⧸ I
  have hI : I ≠ ⊤ := by
    intro h
    rcases Ideal.pow_eq_top_iff.mp h with hmax | hn
    · exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmax
    · exact Nat.succ_ne_zero n hn
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hpow : IsLocalRing.maximalIdeal Q ^ (n + 1) = ⊥ := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  have hnil : IsLocalRing.maximalIdeal Q ≤ nilradical Q := by
    intro x hx
    apply mem_nilradical.mpr
    refine ⟨n + 1, ?_⟩
    have hp := Ideal.pow_mem_pow hx (n + 1)
    rw [hpow] at hp
    exact hp
  have : HenselianRing Q (IsLocalRing.maximalIdeal Q) :=
    HenselianRing.of_le_nilradical (IsLocalRing.maximalIdeal Q) hnil
  refine { is_henselian := ?_ }
  intro f hf a ha hu
  exact HenselianRing.is_henselian f hf a ha
    (hu.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal Q)))

/-- The map on each positive infinitesimal quotient is an actual
isomorphism, with powers of the native maximal ideals on both sides. -/
def ordinaryHenselizationPowQuotientEquiv (n : ℕ) :
    R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1) ≃+*
      ordinaryHenselization R ⧸
        IsLocalRing.maximalIdeal (ordinaryHenselization R) ^ (n + 1) := by
  have : HenselianLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)) :=
    henselianLocalRing_quotient_maximalIdeal_pow R n
  have hmap :
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (ordinaryHenselizationMap R) =
        IsLocalRing.maximalIdeal (ordinaryHenselization R) ^ (n + 1) := by
    rw [Ideal.map_pow]
    exact congrArg (fun I => I ^ (n + 1))
      (geometricStalkStructureMap_map_maximalIdeal (IsLocalRing.residue R))
  exact (ordinaryHenselizationQuotientEquiv R
    (IsLocalRing.maximalIdeal R ^ (n + 1))).trans (Ideal.quotEquivOfEq hmap)

/-- The actual positive-level isomorphism preserves the original
henselization map on representatives. -/
theorem ordinaryHenselizationPowQuotientEquiv_mk (n : ℕ) (a : R) :
    ordinaryHenselizationPowQuotientEquiv R n
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)) a) =
      Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (ordinaryHenselization R) ^ (n + 1))
          (ordinaryHenselizationMap R a) := by
  have : HenselianLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)) :=
    henselianLocalRing_quotient_maximalIdeal_pow R n
  dsimp only [ordinaryHenselizationPowQuotientEquiv, RingEquiv.trans_apply]
  rw [ordinaryHenselizationQuotientEquiv_mk, Ideal.quotEquivOfEq_mk]

end EtaleFundamentalGroups.StrictHenselian
