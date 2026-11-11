/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.AdicCompletion.MapAlongIdeal

/-!
# Uniqueness of local maps out of a completion

Local maps from a Noetherian local ring's completion to a separated local
ring agree when they agree on the original ring. Localness supplies
continuity on every power of the maximal ideal; no topological structure
or additional continuity hypothesis is required.
-/

@[expose] public section

noncomputable section

namespace AdicCompletion

open IsLocalRing

variable {R S : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing S] [IsLocalRing S] [IsHausdorff (maximalIdeal S) S]

/-- Local maps into a separated local ring are determined by their values
on the original ring inside its maximal-adic completion. -/
theorem localHom_ext
    (f g : AdicCompletion (maximalIdeal R) R →+* S)
    [IsLocalHom f] [IsLocalHom g]
    (h : f.comp (algebraMap R (AdicCompletion (maximalIdeal R) R)) =
      g.comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) : f = g := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (maximalIdeal S)
  intro n x
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective
    ((maximalIdeal R) ^ n • (⊤ : Submodule R R)) (x.val n)
  have hd : x - algebraMap R (AdicCompletion (maximalIdeal R) R) r ∈
      (maximalIdeal (AdicCompletion (maximalIdeal R) R)) ^ n := by
    rw [maximalIdeal_eq_map, ← Ideal.map_pow,
      ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
      pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing]
    change eval (maximalIdeal R) R n (x - of (maximalIdeal R) R r) = 0
    rw [map_sub, eval_of]
    exact sub_eq_zero.mpr hr.symm
  have hf : f (x - algebraMap R (AdicCompletion (maximalIdeal R) R) r) ∈
      (maximalIdeal S) ^ n :=
    Ideal.le_comap_pow f n
      (pow_le_pow_left' (maximalIdeal_comap f).symm.le n hd)
  have hg : g (x - algebraMap R (AdicCompletion (maximalIdeal R) R) r) ∈
      (maximalIdeal S) ^ n :=
    Ideal.le_comap_pow g n
      (pow_le_pow_left' (maximalIdeal_comap g).symm.le n hd)
  calc
    Ideal.Quotient.mk ((maximalIdeal S) ^ n) (f x) =
        Ideal.Quotient.mk ((maximalIdeal S) ^ n)
          (f (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) :=
      Ideal.Quotient.eq.mpr (by simpa only [map_sub] using hf)
    _ = Ideal.Quotient.mk ((maximalIdeal S) ^ n)
          (g (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) :=
      congrArg (Ideal.Quotient.mk ((maximalIdeal S) ^ n)) (RingHom.congr_fun h r)
    _ = Ideal.Quotient.mk ((maximalIdeal S) ^ n) (g x) :=
      (Ideal.Quotient.eq.mpr (by simpa only [map_sub] using hg)).symm

end AdicCompletion
