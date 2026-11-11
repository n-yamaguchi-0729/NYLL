/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselizationQuotient
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.CompletionFromQuotientEquivalences

/-!
# The completion of the actual ordinary henselization

The actual henselization map induces isomorphisms on all maximal-ideal
power quotients. The existing compatible-quotient completion construction
then identifies both completions, preserving the original map from the
local ring. No Noetherianity hypothesis is needed for this comparison.
-/

@[expose] public section

noncomputable section

universe u

namespace EtaleFundamentalGroups.StrictHenselian

variable (R : Type u) [CommRing R] [IsLocalRing R]

theorem ordinaryHenselization_map_maximalIdeal_pow (n : ℕ) :
    (IsLocalRing.maximalIdeal R ^ n).map (ordinaryHenselizationMap R) =
      IsLocalRing.maximalIdeal (ordinaryHenselization R) ^ n := by
  rw [Ideal.map_pow]
  exact congrArg (fun I => I ^ n)
    (geometricStalkStructureMap_map_maximalIdeal (IsLocalRing.residue R))

/-- The map on a native adic quotient, including the zero quotient. -/
def ordinaryHenselizationAdicQuotientMap (n : ℕ) :
    R ⧸ IsLocalRing.maximalIdeal R ^ n →+*
      ordinaryHenselization R ⧸
        IsLocalRing.maximalIdeal (ordinaryHenselization R) ^ n :=
  Ideal.quotientMap
    (IsLocalRing.maximalIdeal (ordinaryHenselization R) ^ n)
    (ordinaryHenselizationMap R)
    (Ideal.map_le_iff_le_comap.mp (ordinaryHenselization_map_maximalIdeal_pow R n).le)

theorem ordinaryHenselizationAdicQuotientMap_bijective (n : ℕ) :
    Function.Bijective (ordinaryHenselizationAdicQuotientMap R n) := by
  cases n with
  | zero =>
      have : Subsingleton (R ⧸ IsLocalRing.maximalIdeal R ^ (0 : ℕ)) := by
        rw [pow_zero, Ideal.one_eq_top]
        infer_instance
      have : Subsingleton
          (ordinaryHenselization R ⧸
            IsLocalRing.maximalIdeal (ordinaryHenselization R) ^ (0 : ℕ)) := by
        rw [pow_zero, Ideal.one_eq_top]
        infer_instance
      exact ⟨fun _ _ _ => Subsingleton.elim _ _,
        fun b => ⟨0, Subsingleton.elim _ b⟩⟩
  | succ n =>
      have heq : ordinaryHenselizationAdicQuotientMap R (n + 1) =
          (ordinaryHenselizationPowQuotientEquiv R n).toRingHom := by
        apply Ideal.Quotient.ringHom_ext
        apply RingHom.ext
        intro a
        exact (ordinaryHenselizationPowQuotientEquiv_mk R n a).symm
      rw [heq]
      exact (ordinaryHenselizationPowQuotientEquiv R n).bijective

/-- The isomorphisms of native power quotients are induced by the
original henselization map on every representative. -/
def ordinaryHenselizationAdicQuotientEquiv (n : ℕ) :
    R ⧸ IsLocalRing.maximalIdeal R ^ n ≃+*
      ordinaryHenselization R ⧸
        IsLocalRing.maximalIdeal (ordinaryHenselization R) ^ n :=
  RingEquiv.ofBijective (ordinaryHenselizationAdicQuotientMap R n)
    (ordinaryHenselizationAdicQuotientMap_bijective R n)

theorem ordinaryHenselizationAdicQuotientEquiv_mk (n : ℕ) (a : R) :
    ordinaryHenselizationAdicQuotientEquiv R n
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ n) a) =
      Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (ordinaryHenselization R) ^ n)
          (ordinaryHenselizationMap R a) :=
  rfl

/-- The actual ordinary henselization and the original local ring have
canonically comparable maximal-ideal completions, with the original
structure map retained in the equality. -/
theorem ordinaryHenselization_exists_completionEquiv :
    ∃ E : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal (ordinaryHenselization R))
          (ordinaryHenselization R),
      ∀ a : R,
        E (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) a) =
          algebraMap (ordinaryHenselization R)
            (AdicCompletion (IsLocalRing.maximalIdeal (ordinaryHenselization R))
              (ordinaryHenselization R))
            (ordinaryHenselizationMap R a) :=
  AdicCompletion.exists_ringEquiv_of_quotientEquiv
    (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal (ordinaryHenselization R))
    (ordinaryHenselizationMap R)
    (ordinaryHenselizationAdicQuotientEquiv R)
    (ordinaryHenselizationAdicQuotientEquiv_mk R)

end EtaleFundamentalGroups.StrictHenselian
