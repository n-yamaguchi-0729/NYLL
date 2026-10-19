/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationValuation
import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# A valuation comparison between a coefficient embedding and a rational point

Localize a coefficient algebra at the kernel of a rational point. Its
embedding into the algebraically closed extension field then factors through
a henselian valuation subring of that same field. The residue map of the
constructed factor agrees with the rational point on every coefficient.

This gives an actual local comparison ring for the essential-surjectivity
argument in Stacks Project, Lemma 58.9.3,
https://stacks.math.columbia.edu/tag/0A49. In particular, the residue triangle
is proved from the centre of the valuation; it is not supplied as a hypothesis.
-/

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A rational point and an embedding into an algebraically closed field
admit a henselian valuation comparison in that same field, with both the
generic and the rational-residue triangles fixed. -/
theorem exists_valuation_constant_specialization
    {k A K : Type u} [Field k] [CommRing A] [Field K] [IsAlgClosed K]
    [Algebra k A] [Algebra k K]
    (t : A →ₐ[k] k) (ι : A →ₐ[k] K) (hι : Function.Injective ι) :
    ∃ (V : ValuationSubring K) (g : A →+* V),
      HenselianLocalRing V ∧
      (algebraMap V K).comp g = ι.toRingHom ∧
      (IsLocalRing.residue V).comp g =
        (((IsLocalRing.residue V).comp g).comp (algebraMap k A)).comp t.toRingHom := by
  let p : Ideal A := RingHom.ker t.toRingHom
  have hp : p.IsPrime := RingHom.ker_isPrime t.toRingHom
  let Aₘ : Type u := Localization.AtPrime p
  have hunits : ∀ y : p.primeCompl, IsUnit (ι y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro hy
    have hyzero : (y : A) = 0 := hι (hy.trans (map_zero ι).symm)
    exact y.property (hyzero ▸ p.zero_mem)
  let q : Aₘ →+* K := IsLocalization.lift (S := Aₘ) hunits
  obtain ⟨V, β, _, hHenselian, _, hlocal, hβ, _⟩ :=
    EtaleFundamentalGroups.StrictHenselian.exists_strictlyHenselianValuationFactor q
  have hβlocal : IsLocalHom β := hlocal
  let g : A →+* V := β.comp (algebraMap A Aₘ)
  have hgeneric : (algebraMap V K).comp g = ι.toRingHom := by
    apply RingHom.ext
    intro a
    exact (RingHom.congr_fun hβ (algebraMap A Aₘ a)).trans
      (IsLocalization.lift_eq hunits a)
  have hzero (a : A) (ha : t a = 0) : IsLocalRing.residue V (g a) = 0 := by
    have hap : a ∈ p := RingHom.mem_ker.mpr ha
    have ham : algebraMap A Aₘ a ∈ IsLocalRing.maximalIdeal Aₘ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff Aₘ p a).mpr hap
    exact (IsLocalRing.residue_eq_zero_iff (g a)).mpr
      (map_nonunit β (algebraMap A Aₘ a) ham)
  refine ⟨V, g, hHenselian, hgeneric, ?_⟩
  apply RingHom.ext
  intro a
  have ha : t (a - algebraMap k A (t a)) = 0 := by
    rw [map_sub, t.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hz : IsLocalRing.residue V (g a) -
      IsLocalRing.residue V (g (algebraMap k A (t a))) = 0 := by
    simpa only [map_sub] using hzero (a - algebraMap k A (t a)) ha
  exact sub_eq_zero.mp hz

end AlgebraicGeometry.FiniteEtale
