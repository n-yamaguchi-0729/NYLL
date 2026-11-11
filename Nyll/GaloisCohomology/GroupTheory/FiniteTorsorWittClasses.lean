/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.FiniteTorsorWitt
public import Mathlib.RingTheory.Localization.FractionRing
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters

/-!
# Independence and Frobenius naturality of affine Witt character classes

Equal deck translations give equal classes in the original coefficient
ring. Actual semilinear maps transport both the Witt equation and its deck
character. On an integral cover the zero Witt class detects the trivial
deck character, by embedding in its fraction field.
-/

@[expose] public section

noncomputable section

namespace GaloisCohomology.FiniteTorsor

open ArtinSchreierWittTheory

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] (ρ : G →* (S ≃ₐ[R] S))
  (p m : ℕ) [Fact p.Prime] [CharP R p] [CharP S p]

/-- Truncated Witt vectors modulo the image of Frobenius minus the identity. -/
abbrev WittClasses := TruncatedWittVector p m R ⧸
  ((TruncatedWittVector.map (frobenius R p)).toAddMonoidHom -
    AddMonoidHom.id (TruncatedWittVector p m R)).range

local notation "Q" => WittClasses R p m

variable [Module.FaithfullyFlat R S]

/-- The same deck character gives the same Witt class, independently of
the trace-one section chosen on the actual affine torsor. -/
theorem witt_class_eq_of_translation_eq
    (hinj : Function.Injective (tensorMap R S ρ))
    (a b : TruncatedWittVector p m R) (β γ : TruncatedWittVector p m S)
    (hβ : TruncatedWittVector.map (frobenius S p) β - β =
      TruncatedWittVector.map (algebraMap R S) a)
    (hγ : TruncatedWittVector.map (frobenius S p) γ - γ =
      TruncatedWittVector.map (algebraMap R S) b)
    (htranslation : ∀ g, TruncatedWittVector.map (ρ g).toRingHom β - β =
      TruncatedWittVector.map (ρ g).toRingHom γ - γ) :
    (a : Q) = (b : Q) := by
  have hfixed (g : G) : TruncatedWittVector.map (ρ g).toRingHom (γ - β) = γ - β := by
    rw [map_sub]
    have h := htranslation g
    linear_combination -h
  obtain ⟨c, hc⟩ := exists_witt_base_of_fixed R S ρ p m hinj (γ - β) hfixed
  apply QuotientAddGroup.eq.mpr
  refine ⟨c, ?_⟩
  change TruncatedWittVector.map (frobenius R p) c - c = -a + b
  apply TruncatedWittVector.map_injective (algebraMap R S)
    (FaithfulSMul.algebraMap_injective R S)
  rw [map_sub, ← TruncatedWittVector.map_frobenius]
  simp only [hc, map_sub, map_add, map_neg]
  linear_combination hγ - hβ

omit [Module.FaithfullyFlat R S] [CharP R p] in
/-- A semilinear map compatible with the actual deck actions transports
the original Witt equation and its prescribed character simultaneously. -/
theorem map_witt_equation_and_translation
    (f : R →+* R) (g : S →+* S) (θ : G →* G)
    (hbase : ∀ a, g (algebraMap R S a) = algebraMap R S (f a))
    (haction : ∀ h x, g (ρ h x) = ρ (θ h) (g x))
    (χ : G →* Multiplicative (ZMod (p ^ m)))
    (a : TruncatedWittVector p m R) (β : TruncatedWittVector p m S)
    (hβ : TruncatedWittVector.map (frobenius S p) β - β =
      TruncatedWittVector.map (algebraMap R S) a)
    (htranslation : ∀ h, TruncatedWittVector.map (ρ h).toRingHom β - β =
      constantCast p m S (χ h).toAdd) :
    (TruncatedWittVector.map (frobenius S p) (TruncatedWittVector.map g β) -
        TruncatedWittVector.map g β =
      TruncatedWittVector.map (algebraMap R S) (TruncatedWittVector.map f a)) ∧
    ∀ h, TruncatedWittVector.map (ρ (θ h)).toRingHom (TruncatedWittVector.map g β) -
      TruncatedWittVector.map g β = constantCast p m S (χ h).toAdd := by
  constructor
  · calc
      TruncatedWittVector.map (frobenius S p) (TruncatedWittVector.map g β) -
          TruncatedWittVector.map g β =
        TruncatedWittVector.map g (TruncatedWittVector.map (frobenius S p) β - β) := by
          rw [TruncatedWittVector.map_frobenius, map_sub]
      _ = TruncatedWittVector.map g (TruncatedWittVector.map (algebraMap R S) a) := by rw [hβ]
      _ = TruncatedWittVector.map (algebraMap R S) (TruncatedWittVector.map f a) := by
        apply TruncatedWittVector.ext
        intro i
        simp only [TruncatedWittVector.map_coeff]
        exact hbase (a.coeff i)
  · intro h
    have hact : TruncatedWittVector.map (ρ (θ h)).toRingHom (TruncatedWittVector.map g β) =
        TruncatedWittVector.map g (TruncatedWittVector.map (ρ h).toRingHom β) := by
      apply TruncatedWittVector.ext
      intro i
      simp only [TruncatedWittVector.map_coeff]
      exact (haction h (β.coeff i)).symm
    rw [hact, ← map_sub, htranslation, constantCast_natural]

omit [Module.FaithfullyFlat R S] [CharP R p] in
private theorem exists_constant_of_witt_frobenius_eq [IsDomain S]
    (x : TruncatedWittVector p m S)
    (hx : TruncatedWittVector.map (frobenius S p) x = x) :
    ∃ z : ZMod (p ^ m), constantCast p m S z = x := by
  let F := FractionRing S
  have : CharP F p := charP_of_injective_algebraMap (IsFractionRing.injective S F) p
  have hF : TruncatedWittVector.map (frobenius F p)
      (TruncatedWittVector.map (algebraMap S F) x) =
        TruncatedWittVector.map (algebraMap S F) x := by
    rw [TruncatedWittVector.map_frobenius, hx]
  obtain ⟨z, hz⟩ := ArtinSchreierWittTheory.exists_constant_of_frobenius_eq p m F _ hF
  refine ⟨z, ?_⟩
  apply TruncatedWittVector.map_injective (algebraMap S F) (IsFractionRing.injective S F)
  rw [constantCast_natural]
  exact hz

/-- On an integral affine torsor the original Witt class is zero exactly
when its prescribed deck character is trivial. -/
theorem witt_class_eq_zero_iff_character_eq_one [IsDomain S]
    (hinj : Function.Injective (tensorMap R S ρ))
    (χ : G →* Multiplicative (ZMod (p ^ m)))
    (a : TruncatedWittVector p m R) (β : TruncatedWittVector p m S)
    (hβ : TruncatedWittVector.map (frobenius S p) β - β =
      TruncatedWittVector.map (algebraMap R S) a)
    (htranslation : ∀ g, TruncatedWittVector.map (ρ g).toRingHom β - β =
      constantCast p m S (χ g).toAdd) :
    (a : Q) = 0 ↔ χ = 1 := by
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := (QuotientAddGroup.eq_zero_iff a).mp ha
    change TruncatedWittVector.map (frobenius R p) b - b = a at hb
    have hbmap := congrArg (TruncatedWittVector.map (algebraMap R S)) hb
    rw [map_sub, ← TruncatedWittVector.map_frobenius] at hbmap
    have hdiff : TruncatedWittVector.map (frobenius S p)
        (β - TruncatedWittVector.map (algebraMap R S) b) =
          β - TruncatedWittVector.map (algebraMap R S) b := by
      rw [map_sub]
      linear_combination hβ - hbmap
    obtain ⟨z, hz⟩ := exists_constant_of_witt_frobenius_eq S p m _ hdiff
    apply MonoidHom.ext
    intro g
    change (χ g).toAdd = 0
    apply constantCast_injective p m S
    rw [map_zero, ← htranslation]
    have hfix : TruncatedWittVector.map (ρ g).toRingHom
        (β - TruncatedWittVector.map (algebraMap R S) b) =
          β - TruncatedWittVector.map (algebraMap R S) b := by
      rw [← hz, constantCast_natural]
    have hbase : TruncatedWittVector.map (ρ g).toRingHom
        (TruncatedWittVector.map (algebraMap R S) b) =
          TruncatedWittVector.map (algebraMap R S) b := by
      apply TruncatedWittVector.ext
      intro i
      simp only [TruncatedWittVector.map_coeff]
      exact (ρ g).commutes (b.coeff i)
    rw [map_sub, hbase] at hfix
    linear_combination hfix
  · intro hχ
    have hfixed (g : G) : TruncatedWittVector.map (ρ g).toRingHom β = β := by
      apply sub_eq_zero.mp
      rw [htranslation, hχ]
      exact map_zero (constantCast p m S)
    obtain ⟨b, hb⟩ := exists_witt_base_of_fixed R S ρ p m hinj β hfixed
    apply (QuotientAddGroup.eq_zero_iff a).mpr
    refine ⟨b, ?_⟩
    change TruncatedWittVector.map (frobenius R p) b - b = a
    apply TruncatedWittVector.map_injective (algebraMap R S)
      (FaithfulSMul.algebraMap_injective R S)
    rw [map_sub, ← TruncatedWittVector.map_frobenius, hb]
    exact hβ

end GaloisCohomology.FiniteTorsor
